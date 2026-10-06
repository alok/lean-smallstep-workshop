import Lean
import Inversion
import Smallstep

set_option linter.missingDocs true

/-!
# Regression checks for workshop inversion

The checks import the workshop's actual `Smallstep.lean` definitions.
No exercise file is imported. Proof-state checks test Rocq-style preservation,
equation orientation, naming, and clearing, rather than solving the workshop's
determinism or progress exercises. All named proofs undergo an axiom audit.
-/

namespace InversionTests

open Smallstep Smallstep.Expr

/-- Constructor incompatibility closes a value-of-addition branch. -/
theorem impossibleValue (a b : Expr) (h : Value (add a b)) : False := by
  inversion h

/-- A constant cannot be the source index of any `Step` constructor. -/
theorem impossibleSource (n : Nat) (target : Expr)
    (h : Step (constant n) target) : False := by
  inversion h

/-- Ordinary inversion keeps the original proof and constructor-to-index equation. -/
theorem valueIndex (expression : Expr) (h : Value expression) :
    ∃ n, expression = constant n := by
  inversion h as [n E]
  guard_hyp h : Value expression
  guard_hyp E : constant n = expression
  guard_target = ∃ n, expression = constant n
  exact ⟨n, E.symm⟩

/-- Source injection rewrites the result equation while keeping the original context. -/
theorem constantResultIndex (n m answer : Nat)
    (h : Step (add (constant n) (constant m)) (constant answer)) :
    answer = n + m := by
  inversion h as [nl nr Es Et | l l' r hs Es Et | l r r' hv hs Es Et]
  guard_hyp h : Step (add (constant n) (constant m)) (constant answer)
  guard_hyp Es : nl = n
  guard_hyp Et : n + m = answer
  guard_target = answer = n + m
  exact Et.symm

/-- Equal constructors yield argument equalities without erasing the original proof. -/
theorem equalConstructors (a b c d : Expr)
    (h : add a b = add c d) : a = c ∧ b = d := by
  inversion h
  guard_hyp h : add a b = add c d
  guard_hyp H0 : a = c
  guard_hyp H1 : b = d
  exact ⟨H0, H1⟩

/-- Constructor discrimination also works when the selected proof is equality. -/
theorem distinctConstructors (n : Nat) (a b : Expr)
    (h : constant n = add a b) : False := by
  inversion h

/-- Repeated index occurrences yield two retained component equations. -/
theorem repeatedIndex (a b same : Expr)
    (h : add a b = add same same) : a = b := by
  inversion h
  exact H0.trans H1.symm

/-- Unicode hypothesis names resolve as ordinary local proofs. -/
theorem hypothesisName (a b : Expr) (Hy₂ : Value (add a b)) : False := by
  inversion Hy₂

/-- Escaped identifiers are accepted by the tactic's identifier syntax. -/
theorem escapedHypothesisName (a b : Expr)
    («value proof» : Value (add a b)) : False := by
  inversion «value proof»

/-- Ordinary inversion preserves an existing dependent hypothesis for explicit rewriting. -/
theorem dependentContext (expression : Expr) (h : Value expression)
    (predicate : Expr → Prop) (known : predicate expression) :
    ∃ n, predicate (constant n) := by
  inversion h as [n E]
  guard_hyp known : predicate expression
  refine ⟨n, ?_⟩
  rw [E]
  exact known

/-- A target depending on the selected proof remains valid after inversion. -/
theorem proofDependentTarget (expression : Expr) (h : Value expression) :
    ∃ n, HEq h (Value.constant n) := by
  inversion h as [n E]
  refine ⟨n, ?_⟩
  cases E
  exact HEq.rfl

/-- General `Step` inversion produces exactly three tagged branches with source equations. -/
theorem multipleStepBranches (source target : Expr) (h : Step source target) :
    ∃ a b, source = add a b := by
  inversion h
  case addConstants n m => exact ⟨constant n, constant m, H0.symm⟩
  case stepLeft left reducedLeft right premise =>
    guard_hyp h : Step source target
    guard_hyp premise : Step left reducedLeft
    guard_hyp H0 : add left right = source
    guard_hyp H1 : add reducedLeft right = target
    exact ⟨left, right, H0.symm⟩
  case stepRight left right reducedRight valuePremise stepPremise =>
    guard_hyp valuePremise : Value left
    guard_hyp stepPremise : Step right reducedRight
    guard_hyp H1 : add left reducedRight = target
    exact ⟨left, right, H0.symm⟩

/-- Premise types are rewritten to the original operands in partially fixed `Step` indices. -/
theorem rewrittenStepPremises (left right result : Expr)
    (h : Step (add left right) result) : True := by
  inversion h as [n m Es Et | a a' b hs Es Et | a b b' hv hs Es Et]
  case addConstants => trivial
  case stepLeft =>
    guard_hyp hs : Step left a'
    guard_hyp Et : add a' right = result
    trivial
  case stepRight =>
    guard_hyp hv : Value left
    guard_hyp hs : Step right b'
    guard_hyp Et : add left b' = result
    trivial

/-- Rule premises remain available for a separately requested second inversion. -/
theorem secondInversion (left right result : Expr)
    (h : Step (add left right) result) : True := by
  inversion h as [n m Es Et | a a' b hs Es Et | a b b' hv hs Es Et]
  case addConstants => trivial
  case stepLeft => trivial
  case stepRight =>
    inversion hv as [n E]
    guard_hyp hv : Value left
    guard_hyp hs : Step right b'
    guard_hyp E : constant n = left
    trivial

/-- Inversion changes only the focused goal and preserves its siblings. -/
theorem siblingGoals (n : Nat) (h : Value (constant n)) : True ∧ True := by
  constructor
  · inversion h
    trivial
  · exact True.intro

/-- Equal constructors at one type support homogeneous heterogeneous equality. -/
theorem homogeneousHEq (a b : Nat) (h : HEq (Nat.succ a) (Nat.succ b)) :
    a = b := by
  inversion h
  guard_hyp h : HEq (Nat.succ a) (Nat.succ b)
  exact H0

/-- An indexed relation whose equation requires arithmetic reasoning. -/
inductive DoubleIndex : Nat → Prop where
  /-- Addition indices need not be constructor-headed. -/
  | at (n : Nat) : DoubleIndex (n + n)

/-- Function-headed index equations are retained in constructor-to-original orientation. -/
theorem residualIndexEquation (n : Nat) (h : DoubleIndex (n + n)) :
    ∃ m, n + n = m + m := by
  inversion h as [m E]
  guard_hyp h : DoubleIndex (n + n)
  guard_hyp E : m + m = n + n
  exact ⟨m, E.symm⟩

/-- Ordinary inversion preserves an existing hypothesis depending on the original proof. -/
theorem residualProofDependentContext (n : Nat) (h : DoubleIndex (n + n))
    (predicate : ∀ i, DoubleIndex i → Prop) (known : predicate (n + n) h) :
    predicate (n + n) h := by
  inversion h
  guard_hyp known : predicate (n + n) h
  exact known

/-- Two indices test discrimination after an earlier arithmetic equation stalls. -/
inductive TwoIndices : Nat → Bool → Prop where
  /-- A constructor compatible with `true`. -/
  | at (n : Nat) : TwoIndices (n + n) true
  /-- A constructor incompatible with `true`. -/
  | incompatible (n : Nat) : TwoIndices (n + n) false

/-- An unresolved first equation does not stop later constructor discrimination. -/
theorem residualWithImpossibleBranch (n : Nat) (h : TwoIndices (n + n) true) :
    ∃ m, n + n = m + m := by
  inversion h as [m E Flag | m E Flag]
  case «at» => exact ⟨m, E.symm⟩

/-- Multiple branches retain individual index constraints and case tags. -/
theorem residualMultipleBranches (n : Nat) (flag : Bool) (h : TwoIndices (n + n) flag) :
    ∃ m, n + n = m + m := by
  inversion h as [m E Flag | m E Flag]
  case «at» =>
    guard_hyp Flag : true = flag
    exact ⟨m, E.symm⟩
  case incompatible =>
    guard_hyp Flag : false = flag
    exact ⟨m, E.symm⟩

/-- A relation supplying a premise as well as an arithmetic index. -/
inductive GuardedIndex : Nat → Prop where
  /-- The premise remains available after its index equation stalls. -/
  | fromWitness (n : Nat) (premise : n = 0) : GuardedIndex (n + n)

/-- A residual branch exposes its ordinary rule premise. -/
theorem residualKeepsPremise (n : Nat) (h : GuardedIndex (n + n)) :
    ∃ m, m = 0 ∧ n + n = m + m := by
  inversion h as [m premise E]
  exact ⟨m, premise, E.symm⟩

/-- An outer constructor around an arithmetic index tests nested injection. -/
inductive WrappedIndex : Nat → Prop where
  /-- Successor is injected before the inner arithmetic equation is retained. -/
  | at (n : Nat) : WrappedIndex (Nat.succ (n + n))

/-- Constructor injection preserves a remaining function-headed equation. -/
theorem residualInsideConstructor (n : Nat) (h : WrappedIndex (Nat.succ (n + n))) :
    ∃ m, n + n = m + m := by
  inversion h as [m E]
  guard_hyp E : m + m = n + n
  exact ⟨m, E.symm⟩

/-- Inversion retains equality of function results without asserting function injectivity. -/
theorem arbitraryFunctionEquality (f : Nat → Nat) (a b : Nat) (h : f a = f b) :
    f b = f a := by
  inversion h
  guard_hyp h : f a = f b
  guard_hyp H0 : f a = f b
  exact H0.symm

/-- Nonindexed propositions preserve their original proof and named constructor premises. -/
theorem nonindexedBranches (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  inversion h as [hp | hq]
  case inl =>
    guard_hyp h : P ∨ Q
    exact Or.inr hp
  case inr =>
    guard_hyp h : P ∨ Q
    exact Or.inl hq

/-- Automatic equation names avoid existing `H0` and `H1` hypotheses. -/
theorem freshEquationNames (t : Expr) (h : Value t) (H0 H1 : True) : True := by
  inversion h
  case constant n =>
    guard_hyp H0 : True
    guard_hyp H1 : True
    guard_hyp H2 : constant n = t
    have _ := H1
    exact H0

/-- An underscore in `as` requests a fresh constructor name without losing the equation name. -/
theorem underscoreNaming (t : Expr) (h : Value t) : ∃ n, t = constant n := by
  inversion h as [_ E]
  case constant n => exact ⟨n, E.symm⟩

/-- Clearing inversion substitutes into the goal and clears its original proof and equations. -/
theorem clearValueTarget (t : Expr) (h : Value t) : ∃ n, t = constant n := by
  inversion_clear h as [n E]
  fail_if_success guard_hyp h : Value t
  fail_if_success guard_hyp E : constant n = t
  guard_target = ∃ m, constant n = constant m
  exact ⟨n, rfl⟩

/-- Unused constructor data is removed by clearing inversion. -/
theorem clearUnusedWitness (t : Expr) (h : Value t) : True := by
  inversion_clear h as [n E]
  fail_if_success guard_hyp n : Nat
  fail_if_success guard_hyp h : Value t
  trivial

/-- Clearing keeps rule premises and rewrites original operands to constructor expressions. -/
theorem clearStepPremises (left right result : Expr)
    (h : Step (add left right) result) : True := by
  inversion_clear h as [n m Es Et | a a' b hs Es Et | a b b' hv hs Es Et]
  case addConstants =>
    fail_if_success guard_hyp h : Step (add left right) result
    fail_if_success guard_hyp n : Nat
    fail_if_success guard_hyp m : Nat
    trivial
  case stepLeft =>
    guard_hyp hs : Step left a'
    fail_if_success guard_hyp Es : a = left
    fail_if_success guard_hyp Et : add a' right = result
    trivial
  case stepRight =>
    guard_hyp hv : Value left
    guard_hyp hs : Step right b'
    fail_if_success guard_hyp h : Step (add left right) result
    trivial

/-- Clearing rewrites existing dependent hypotheses, then drops the equations. -/
theorem clearDependentContext (t : Expr) (h : Value t)
    (predicate : Expr → Prop) (known : predicate t) : ∃ n, predicate (constant n) := by
  inversion_clear h as [n E]
  guard_hyp known : predicate (constant n)
  exact ⟨n, known⟩

/-- Constructor equality can also be inverted and cleared. -/
theorem clearEquality (a b c d : Expr) (h : add a b = add c d) : a = c ∧ b = d := by
  inversion_clear h
  fail_if_success guard_hyp h : add a b = add c d
  exact ⟨rfl, rfl⟩

/-- The ordinary inversion/substitution sequence translates Rocq's common idiom. -/
theorem explicitSubstitution (t : Expr) (h : Value t) : ∃ n, t = constant n := by
  inversion h
  subst_vars
  case constant n => exact ⟨n, rfl⟩

-- Invalid inputs and naming clauses must fail without changing the goal.
example (_n : Nat) : True := by
  fail_if_success inversion _n
  trivial

example (P : Prop) (_h : P) : True := by
  fail_if_success inversion _h
  trivial

example : True := by
  fail_if_success inversion True.intro
  fail_if_success inversion noSuchHypothesis
  trivial

example (P Q : Prop) (_h : P ∨ Q) : True := by
  fail_if_success inversion _h as [hp]
  fail_if_success inversion _h as [hp extra | hq]
  guard_hyp _h : P ∨ Q
  trivial

example (t : Expr) (_h : Value t) : True := by
  fail_if_success inversion _h as [n E excess]
  guard_hyp _h : Value t
  trivial

-- A proof-dependent hypothesis prevents clearing its original proof; failure rolls back.
example (t : Expr) (h : Value t) (predicate : Value t → Prop)
    (known : predicate h) : predicate h := by
  fail_if_success inversion_clear h
  guard_hyp known : predicate h
  exact known

-- Constructor and equality budgets are checked transactionally.
set_option tactic.inversion.maxConstructors 1 in
example (_h : True ∨ True) : True := by
  fail_if_success inversion _h
  guard_hyp _h : True ∨ True
  trivial

set_option tactic.inversion.maxEquations 1 in
example (n : Nat) (_h : WrappedIndex (Nat.succ (n + n))) : True := by
  fail_if_success inversion _h
  guard_hyp _h : WrappedIndex (Nat.succ (n + n))
  trivial

set_option tactic.inversion.maxRecDepth 0 in
example (h : True) : True := by
  fail_if_success inversion h
  exact h

set_option tactic.inversion.maxHeartbeats 0 in
example (h : True) : True := by
  fail_if_success inversion h
  exact h

set_option tactic.inversion.maxEquations 0 in
example (h : True) : True := by
  fail_if_success inversion h
  exact h

end InversionTests
