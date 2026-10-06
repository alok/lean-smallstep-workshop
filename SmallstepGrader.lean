import Lean

set_option linter.missingDocs true

/-!
# Lean companion proof checker

This is a Lean-only checker, not the official Software Foundations Rocq grader.
It checks a declaration's expected type and its transitive axiom dependencies.
Only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms are
allowed. In particular, a `sorry` in a helper theorem still fails the check.
-/

open Lean Elab Command Meta

/-- Lean-only command checking an expected theorem type and transitive axiom dependencies. -/
syntax (name := checkProof) "#check_proof " ident " : " term : command

/-- Lean-only implementation of `#check_proof`; it does not construct or modify proofs. -/
@[command_elab checkProof] private def elabCheckProof : CommandElab
  | `(#check_proof $declaration:ident : $expectedType:term) => do
    let name := declaration.getId
    let typeMatches ← liftTermElabM do
      let expected ← Term.elabType expectedType
      Term.synthesizeSyntheticMVarsNoPostponing
      let actual ← mkConstWithFreshMVarLevels name
      isDefEq (← inferType actual) expected
    let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
    let forbidden := (← collectAxioms name).filter fun dependency => !allowed.contains dependency
    if !typeMatches then
      logError m!"FAIL {name}: theorem type does not match the expected exercise statement"
    else if !forbidden.isEmpty then
      logError m!"FAIL {name}: forbidden axioms {forbidden}"
    else
      logInfo m!"PASS {name}: expected type and axiom check"
  | _ => throwUnsupportedSyntax
