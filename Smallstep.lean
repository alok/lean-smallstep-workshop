import Std

set_option linter.missingDocs true

/-!
# Smallstep: a Lean 4 follow-along

Source chapter: Software Foundations, Programming Language Foundations,
https://softwarefoundations.cis.upenn.edu/plf-current/Smallstep.html

This is a short companion, not a translation of the whole chapter.
It covers the constants/addition language, the value-aware step rules,
and reflexive-transitive closure. No Mathlib dependency is needed.

Read alongside “A Toy Language”, “Values”, and “Multi-Step Reduction”.
The chapter's initial ST_P2 has a literal constant on the left; below we
use its later version with an explicit Value premise. For this language
these describe the same evaluation order.

Check this file with: lake build
Exercise holes are in SmallstepExercises.lean, not in this file.
-/

namespace Smallstep

/-- Expressions containing constants and addition. SF original: `tm`; its constructors are `C` and `P`. -/
inductive Expr where
  /-- A literal natural number. SF original: `C`; its numeric argument corresponds to `n`. -/
  | constant : Nat → Expr
  /-- An addition expression. SF original: `P`; its left/right operands correspond to `t₁`/`t₂`. -/
  | add : Expr → Expr → Expr
  deriving Repr, DecidableEq

open Expr

/-- Compute the final number all at once. SF original: `evalF`; the input is SF's `t`.
In the equations, `number ↔ n`, `left ↔ t₁`, and `right ↔ t₂`. -/
def evaluate : Expr → Nat
  | constant number => number
  | add left right => evaluate left + evaluate right

/-- An expression is finished evaluating. SF original: `value`; its expression argument is SF's `t`. -/
inductive Value : Expr → Prop where
  /-- A constant is already a value. SF original: `v_C`; `number ↔ n`. -/
  | constant (number : Nat) : Value (Expr.constant number)

/-- One left-to-right computation step. SF original: the value-aware `step` in “Values”.
Its starting/result expression arguments correspond to `t`/`t'`. -/
inductive Step : Expr → Expr → Prop where
  /-- Add two literals in one step. SF original: `ST_PCC`;
  `leftNumber ↔ n₁`, `rightNumber ↔ n₂`. -/
  | addConstants (leftNumber rightNumber : Nat) :
      Step (add (constant leftNumber) (constant rightNumber))
        (constant (leftNumber + rightNumber))
  /-- Lift a left-operand step into addition. SF original: `ST_P1`;
  `left ↔ t₁`, `reducedLeft ↔ t₁'`, `right ↔ t₂`.
  `leftStep` proves the original premise `t₁ --> t₁'`. -/
  | stepLeft {left reducedLeft right : Expr} (leftStep : Step left reducedLeft) :
      Step (add left right) (add reducedLeft right)
  /-- Step the right operand after the left is a value. SF original: value-aware `ST_P2`;
  `left ↔ v₁`, `right ↔ t₂`, `reducedRight ↔ t₂'`.
  `leftIsValue` proves `value v₁`; `rightStep` proves `t₂ --> t₂'`. -/
  | stepRight {left right reducedRight : Expr}
      (leftIsValue : Value left) (rightStep : Step right reducedRight) :
      Step (add left right) (add left reducedRight)

-- SF uses -->; Lean treats adjacent -- as a line comment.
-- A space between the hyphens keeps the chapter's arrow parser-safe: - ->.
/-- One reduction step. SF original notation: `t --> t'` for `step t t'`;
`expression ↔ t`, `result ↔ t'`. -/
infix:50 " →ₛ " => Step
/-- SF notation `t --> t'` for `step t t'`, with a space to avoid Lean's line comment.
`expression ↔ t`, `result ↔ t'`. -/
notation:40 expression:41 " - " "-> " result:41 => Step expression result

#check Step.addConstants
#check Step.stepLeft
#check Step.stepRight

/-- Reduce the left inner addition once. SF original: `SimpleArith1.test_step_1`,
here stated using the equivalent value-aware rules. -/
theorem leftStepExample :
    add (add (constant 1) (constant 3)) (add (constant 2) (constant 4)) - ->
    add (constant 4) (add (constant 2) (constant 4)) := by
  apply Step.stepLeft
  exact Step.addConstants 1 3

/-- Zero or more steps of any relation. SF original: `multi`;
`State ↔ X`, `relation ↔ R`. -/
inductive Multi {State : Type u} (relation : State → State → Prop) :
    State → State → Prop where
  /-- Zero steps leave a state unchanged. SF original: `multi_refl`; `state ↔ x`. -/
  | reflexive (state : State) : Multi relation state state
  /-- Prepend one step to a sequence. SF original: `multi_step`;
  `start ↔ x`, `intermediate ↔ y`, `finish ↔ z`.
  `firstStep` proves `R x y`; `remainingSteps` proves `multi R y z`. -/
  | prependStep {start intermediate finish : State}
      (firstStep : relation start intermediate)
      (remainingSteps : Multi relation intermediate finish) :
      Multi relation start finish

/-- Lean-only abbreviation for SF's `multi step`: zero or more small steps.
It names a specialization, rather than a separately named SF definition. -/
abbrev MultiStep : Expr → Expr → Prop := Multi Step
/-- Zero or more reduction steps. SF original notation: `t -->* t'` for `multi step t t'`;
`expression ↔ t`, `result ↔ t'`. -/
infix:50 " →ₛ* " => MultiStep
/-- SF notation `t -->* t'` for `multi step t t'`, with a space to avoid Lean's line comment.
`expression ↔ t`, `result ↔ t'`. -/
notation:40 expression:41 " - " "->* " result:41 => MultiStep expression result

/-- Lean-only two-step worked example; no exact named SF counterpart.
It illustrates SF's `multi` construction; the final reflexive case contributes zero steps. -/
theorem twoStepExample :
    add (add (constant 1) (constant 3)) (constant 2) - ->* constant 6 := by
  apply Multi.prependStep (Step.stepLeft (Step.addConstants 1 3))
  exact Multi.prependStep (Step.addConstants 4 2) (Multi.reflexive (constant 6))

-- Lean-only equality-rewriting example; no named SF counterpart.
example (left replacement right : Expr) (sameExpression : left = replacement) :
    add left right = add replacement right := by
  rw [sameExpression]

/-!
## Rocq / Coq → Lean quick map

  Inductive tm : Type := ...       inductive Expr where ...
  C n                             Expr.constant number
  P t₁ t₂                         Expr.add left right
  evalF                           evaluate
  v_C                             Value.constant
  ST_PCC                          Step.addConstants
  ST_P1                           Step.stepLeft
  ST_P2                           Step.stepRight
  multi_refl                      Multi.reflexive
  multi_step                      Multi.prependStep
  nat                             Nat
  Definition / Fixpoint           def (recursive equations are allowed)
  Module                          namespace
  Theorem name : statement.       theorem name : statement := by
  intros x H                      intro expression hypothesis
  apply ST_P1                     apply Step.stepLeft
  exact H                         exact hypothesis
  reflexivity                     rfl
  rewrite H                       rw [hypothesis]
  rewrite <- H                    rw [← hypothesis]
  destruct H                      cases hypothesis
  induction H                     induction hypothesis
  Admitted                        sorry (an unchecked proof placeholder)

These are starting points, not exact tactic-for-tactic equivalences.
Lean `cases` on an indexed relation often handles impossible cases that
Rocq proofs eliminate with `inversion`; some goals need more explicit
case handling. Lean `simp` and Rocq `simpl` also have different behavior.

IMPORTANT: `- ->` is a relation, not equality. Use Step constructors to
justify a reduction. Use `rw` with equality proofs. Notation changes how
a judgment looks; it does not turn semantic reduction into equality.

Editor: keep Lean's Infoview open and place the cursor after each tactic.
The notation declarations above render the spaced SF arrows directly in goals.
-/

end Smallstep
