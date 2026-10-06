import Lean.Elab.Tactic.ElabTerm
import Lean.Meta.Tactic.Cases
import Lean.Meta.Tactic.Rewrite
import Lean.Meta.Tactic.Replace

set_option linter.missingDocs true

/-!
# A workshop `inversion` tactic

Version 3 follows ordinary Rocq inversion for the Smallstep port. `inversion h`
keeps the original proof and indices, introduces constructor premises, and
retains useful constructor/index equalities. It rewrites newly derived premises
using those equalities without substituting away the original context. Thus
`inversion h; subst_vars` is the usual counterpart of `inversion H; subst`.

`inversion_clear h` rewrites with the derived equalities, clears them and `h`,
and removes unused constructor data. `inversion h as [n E]` names constructor
arguments followed by index equations; use `|` to separate constructor branches.
An injected equation gives its requested name to the first component, with
fresh names for the remaining components. `_` requests an automatic name.

The kernel checks every recursor, no-confusion, and equality-rewriting term.
No rule premises are recursively inverted. Function-headed equations remain as
hypotheses rather than causing failure. Automatic names and hypothesis order
can differ from Rocq; generalized dependent indices and nested `as` patterns
are not a full Rocq port. Clearing fails if the original proof is still needed
by a dependent target or hypothesis. General heterogeneous equations may remain
unresolved. The usual constructor case tags are available for `case`.

The options below cap constructor count, recursion depth, and elaborator work.
The standard `maxRecDepth` and `maxHeartbeats` limits are also respected when
they are smaller and nonzero. Failure leaves no accepted partial proof.
-/

namespace WorkshopInversion

open Lean Meta Elab Tactic

/-- Maximum number of constructors considered by one `inversion` (default 32). -/
register_option tactic.inversion.maxConstructors : Nat := {
  defValue := 32
  descr := "maximum constructor count for the workshop inversion tactic"
}

/-- Recursion-depth cap for one `inversion`, including core equality elimination (default 256). -/
register_option tactic.inversion.maxRecDepth : Nat := {
  defValue := 256
  descr := "recursion-depth cap for the workshop inversion tactic; must be positive"
}

/-- Work cap for one `inversion`, in Lean's `maxHeartbeats` units (default 20000). -/
register_option tactic.inversion.maxHeartbeats : Nat := {
  defValue := 20000
  descr := "heartbeat cap for the workshop inversion tactic; must be positive"
}

/-- Maximum equality-processing steps per inversion branch (default 256). -/
register_option tactic.inversion.maxEquations : Nat := {
  defValue := 256
  descr := "maximum equality-processing steps per inversion branch; must be positive"
}

private def boundedLimit (existing cap : Nat) : Nat :=
  if existing == 0 then cap else min existing cap

/-- Roll back failed core elimination; preserve cancellation and resource-limit exceptions. -/
private def tryElimination? (action : MetaM α) : MetaM (Option α) := do
  try
    return some (← commitIfNoEx action)
  catch ex =>
    match ex with
    | .error .. =>
      if ex.isRuntime then throw ex
      return none
    | .internal .. => throw ex

private def freshEquationName (goal : MVarId) : MetaM Name := goal.withContext do
  let context ← getLCtx
  let rec find (fuel index : Nat) : MetaM Name := do
    match fuel with
    | 0 => throwError "inversion fresh-name limit exceeded"
    | fuel + 1 =>
      let name := Name.mkSimple s!"H{index}"
      if context.usesUserName name then find fuel (index + 1) else return name
  find 4096 0

private def equationName (goal : MVarId) (preferred : Name := .anonymous) : MetaM Name :=
  if preferred.isAnonymous then freshEquationName goal else return preferred

private def remapId (subst : FVarSubst) (id : FVarId) : FVarId :=
  (subst.apply (mkFVar id)).fvarId!

/-- Rewrite proof types without eliminating the data variables they mention. -/
private def rewriteProofs (goal : MVarId) (equation : FVarId)
    (originals : FVarIdSet) (symm : Bool) : MetaM (MVarId × FVarSubst) := do
  let mut goal := goal
  let mut subst : FVarSubst := {}
  let declarations ← goal.withContext do return (← getLCtx).getFVarIds
  for id in declarations do
    let id := remapId subst id
    let currentEquation := remapId subst equation
    if id == currentEquation || originals.contains id then continue
    let replacement? ← tryElimination? <| goal.withContext do
      unless ← isProp (← id.getType) do throwError "not a proof"
      let result ← goal.rewrite (← id.getType) (mkFVar currentEquation) symm
      unless result.mvarIds.isEmpty do throwError "inversion rewrite produced side goals"
      goal.replaceLocalDecl id result.eNew result.eqProof
    if let some replacement := replacement? then
      goal := replacement.mvarId
      let replacementSubst := replacement.subst.insert id (mkFVar replacement.fvarId)
      subst := subst.append replacementSubst
  if let some replacement ← tryElimination? <| goal.withContext do
      let result ← goal.rewrite (← goal.getType) (mkFVar (remapId subst equation)) symm
      unless result.mvarIds.isEmpty do throwError "inversion rewrite produced side goals"
      goal.replaceTargetEq result.eNew result.eqProof then
    goal := replacement
  return (goal, subst)

private def introduceEquations (goal : MVarId) (count : Nat)
    (names : List Name := []) : MetaM (List FVarId × MVarId) := do
  let mut goal := goal
  let mut names := names
  let mut equations := []
  for _ in [:count] do
    let preferred := names.headD .anonymous
    names := names.drop 1
    let (equation, next) ← goal.intro (← equationName goal preferred)
    goal := next
    equations := equations ++ [equation]
  return (equations, goal)

/-- Reverse a generated index equation into Rocq's constructor-to-original orientation. -/
private def reverseEquation (goal : MVarId) (equation : FVarId) : MetaM (FVarId × MVarId) :=
  goal.withContext do
    let proof ← if (← equation.getType).isHEq then
      mkAppM ``HEq.symm #[mkFVar equation]
    else
      mkEqSymm (mkFVar equation)
    let name := (← equation.getDecl).userName
    let goal ← goal.assert name (← inferType proof) proof
    let (reversed, goal) ← goal.intro name
    return (reversed, ← goal.tryClear equation)

/-- Inject constructors and rewrite fresh rule variables, while retaining useful equations. -/
private def processEquations : Nat → List FVarId → Array FVarId → MVarId → FVarIdSet →
    MetaM (Option (MVarId × Array FVarId))
  | _, [], retained, goal, _ => return some (goal, retained)
  | 0, _, _, _, _ => throwError "inversion equation-processing limit exceeded"
  | fuel + 1, equation :: rest, retained, goal, originals => goal.withContext do
    let (equation, goal) ←
      if let some converted ← tryElimination? (heqToEq goal equation) then
        pure converted
      else pure (equation, goal)
    goal.withContext do
    let type ← whnf (← equation.getType)
    let some (_, lhs, rhs) := type.eq? |
      processEquations fuel rest (retained.push equation) goal originals
    if ← isDefEq lhs rhs then
      return ← processEquations fuel rest retained (← goal.tryClear equation) originals
    let lhs ← whnf lhs
    let rhs ← whnf rhs
    if ← isConstructorApp lhs <&&> isConstructorApp rhs then
      let name := (← equation.getDecl).userName
      match ← injectionCore goal equation with
      | .solved => return none
      | .subgoal goal count =>
        let (newEquations, goal) ← introduceEquations goal count [name]
        return ← processEquations fuel (newEquations ++ rest) retained goal originals
    let symm? :=
      if lhs.isFVar && !originals.contains lhs.fvarId! && !rhs.containsFVar lhs.fvarId! then
        some false
      else if rhs.isFVar && !originals.contains rhs.fvarId! && !lhs.containsFVar rhs.fvarId! then
        some true
      else none
    if let some symm := symm? then
      let (goal, subst) ← rewriteProofs goal equation originals symm
      return ← processEquations fuel (rest.map (remapId subst))
        ((retained.push equation).map (remapId subst)) goal originals
    processEquations fuel rest (retained.push equation) goal originals

private def clearInversion (goal : MVarId) (hypothesis : FVarId)
    (equations : Array FVarId) (originals : FVarIdSet) : MetaM MVarId := do
  let mut goal ← goal.clear hypothesis
  let mut equations := equations
  for i in [:equations.size] do
    let equation := equations[i]!
    let type ← goal.withContext do return (← equation.getType)
    if let some (_, lhs, _rhs) := type.eq? then
      let symm := !(lhs.isFVar && !originals.contains lhs.fvarId!)
      let (next, subst) ← rewriteProofs goal equation {} symm
      goal := next
      equations := equations.map (remapId subst)
      goal ← goal.tryClear equations[i]!
  let declarations ← goal.withContext do return (← getLCtx).getFVarIds
  for id in declarations.reverse do
    if originals.contains id then continue
    if ← goal.withContext do isProp (← id.getType) then continue
    goal ← goal.tryClear id
  return goal

private def invertProof (goal : MVarId) (hypothesis : FVarId) (info : InductiveVal)
    (fuel : Nat) (givenNames : Array AltVarNames) (equationNames : Array (List Name))
    (clear : Bool) : MetaM (Array CasesSubgoal) := goal.withContext do
  let originals := (← getLCtx).getFVarIds.foldl (fun set id => set.insert id) ({} : FVarIdSet)
  let type ← whnf (← hypothesis.getType)
  if type.isEq || type.isHEq then
    let preferred := equationNames[0]?.getD [] |>.headD .anonymous
    let name ← equationName goal preferred
    let goal ← goal.assert name type (mkFVar hypothesis)
    let (equation, goal) ← goal.intro1P
    let some (goal, retained) ← processEquations fuel [equation] #[] goal originals |
      return #[]
    let goal ← if clear then clearInversion goal hypothesis retained originals else pure goal
    return #[{ mvarId := goal, ctorName := some ``Eq.refl }]
  let (branches, numEquations) ← (if info.numIndices == 0 then do
    let goal ← goal.assert `inversionMajor type (mkFVar hypothesis)
    let (copy, goal) ← goal.intro1
    pure (← goal.cases copy givenNames, 0)
  else do
    let generalized ← generalizeIndices goal hypothesis
    pure (← generalized.mvarId.cases generalized.fvarId givenNames, info.numIndices)
    : MetaM (Array CasesSubgoal × Nat))
  branches.filterMapM fun branch => do
    let index := branch.ctorName.bind (fun name => info.ctors.findIdx? (· == name)) |>.getD 0
    let (equations, goal) ← introduceEquations branch.mvarId numEquations
      (equationNames[index]?.getD [])
    let goal ← if numEquations == 0 then pure goal else goal.intro1_
    let mut goal := goal
    let mut reversed := []
    for equation in equations do
      let (equation, next) ← reverseEquation goal equation
      goal := next
      reversed := reversed ++ [equation]
    let some (finalGoal, retained) ← processEquations fuel reversed #[] goal originals |
      return none
    let finalGoal ← if clear then clearInversion finalGoal hypothesis retained originals else pure finalGoal
    return some { branch with mvarId := finalGoal }

/-- Flat constructor-argument and equation names in one Rocq-style inversion branch. -/
declare_syntax_cat inversionBranchNames
/-- Whitespace-separated identifiers or `_` placeholders in an inversion branch. -/
syntax (binderIdent)* : inversionBranchNames

/-- Rocq-style naming for all constructor branches, separated by `|`. -/
declare_syntax_cat inversionNaming
/-- The `as [names | names]` clause of an inversion tactic. -/
syntax "as" "[" inversionBranchNames ("|" inversionBranchNames)* "]" : inversionNaming

/-- Invert a local inductive proof, retaining the original proof and useful index equations. -/
syntax (name := inversion) "inversion " ident (ppSpace inversionNaming)? : tactic

/-- Invert a local inductive proof, then rewrite and clear its proof and index equations. -/
syntax (name := inversionClear) "inversion_clear " ident (ppSpace inversionNaming)? : tactic

private def parseNaming (info : InductiveVal) (naming : Option Syntax) :
    TacticM (Array AltVarNames × Array (List Name)) := do
  let some naming := naming | return (#[], #[])
  let branches ← match naming with
    | `(inversionNaming| as [$first:inversionBranchNames $[| $rest:inversionBranchNames]*]) =>
      pure (#[first] ++ rest)
    | _ => throwUnsupportedSyntax
  unless branches.size == info.ctors.length do
    throwError "inversion as expects {info.ctors.length} constructor branches, got {branches.size}"
  let mut givenNames := #[]
  let mut equationNames := #[]
  for branch in branches, constructor in info.ctors do
    let names ← match branch with
      | `(inversionBranchNames| $[$names:binderIdent]*) =>
        pure (names.toList.map fun name =>
          if name.raw[0].isIdent then name.raw[0].getId else Name.mkSimple "_")
      | _ => throwUnsupportedSyntax
    let constructor ← getConstInfoCtor constructor
    unless names.length ≤ constructor.numFields + info.numIndices do
      throwError "too many inversion as names for constructor {constructor.name}"
    givenNames := givenNames.push { varNames := names.take constructor.numFields, explicit := true }
    equationNames := equationNames.push (names.drop constructor.numFields |>.map fun name =>
      if name == Name.mkSimple "_" then .anonymous else name)
  return (givenNames, equationNames)

private def runInversion (hypothesis : Syntax) (naming : Option Syntax) (clear : Bool) :
    TacticM Unit := withMainContext do
  let opts ← getOptions
  let depth := tactic.inversion.maxRecDepth.get opts
  let heartbeats := tactic.inversion.maxHeartbeats.get opts
  let equations := tactic.inversion.maxEquations.get opts
  if depth == 0 || heartbeats == 0 || equations == 0 then
    throwError "inversion resource limits must be positive"
  let boundedOpts := opts
    |>.set `maxRecDepth (boundedLimit (maxRecDepth.get opts) depth)
    |>.set `maxHeartbeats (boundedLimit (maxHeartbeats.get opts) heartbeats)
  withOptions (fun _ => boundedOpts) <|
    withTheReader Core.Context (fun ctx =>
      { ctx with
          maxRecDepth := maxRecDepth.get boundedOpts
          maxHeartbeats := Core.getMaxHeartbeats boundedOpts }) <|
    withCurrHeartbeats do
    let fvarId ← getFVarId hypothesis
    let type ← whnf (← fvarId.getType)
    unless ← isProp type do
      throwErrorAt hypothesis "inversion expects a proof of an inductive proposition"
    let .const inductiveName _ := type.getAppFn |
      throwErrorAt hypothesis "inversion expects a proof of an inductive proposition"
    let .inductInfo info ← getConstInfo inductiveName |
      throwErrorAt hypothesis "inversion expects a proof of an inductive proposition"
    let maxConstructors := tactic.inversion.maxConstructors.get opts
    if info.ctors.length > maxConstructors then
      throwErrorAt hypothesis
        "inversion constructor limit exceeded ({info.ctors.length} > {maxConstructors})"
    let (givenNames, equationNames) ← parseNaming info naming
    liftMetaTactic fun goal => do
      let tag ← goal.getTag
      let branches ← commitIfNoEx <|
        invertProof goal fvarId info equations givenNames equationNames clear
      for branch in branches do
        if let some constructor := branch.ctorName then
          branch.mvarId.setTag (tag ++ constructor)
      pure (branches.toList.map (·.mvarId))

elab_rules : tactic
  | `(tactic| inversion $hypothesis:ident $[$naming:inversionNaming]?) =>
    runInversion hypothesis (naming.map (·.raw)) false
  | `(tactic| inversion_clear $hypothesis:ident $[$naming:inversionNaming]?) =>
    runInversion hypothesis (naming.map (·.raw)) true

end WorkshopInversion
