import Smallstep
import Inversion

set_option linter.missingDocs true

/-!
# Exercises: YOUR proof work goes here

Every `sorry` below is deliberately unfinished. Lean can accept these
with warnings; acceptance does not mean the exercises have been proved.
The worked examples in Smallstep.lean do not depend on these holes.

From this project's folder:
  lake build
  lake env lean SmallstepExercises.lean

Follow the chapter's corresponding exercise when you reach it. The
strong-progress statement is also included as optional practice; the
chapter gives a worked proof, but it is not filled in here.

In Cursor, run “Lean 4: Toggle Infoview” from the Command Palette.
Place the cursor at a `sorry` to see the goal. Replace one hole at a time.
-/

namespace Smallstep
open Expr

/-- Step the right operand with a finished left operand. SF original:
`SimpleArith1.test_step_2`, adapted here to the equivalent value-aware `Step`. -/
theorem rightStepExercise :
    add (constant 0) (add (constant 2) (add (constant 1) (constant 3))) - ->
    add (constant 0) (add (constant 2) (constant 4)) := by
  sorry

-- SF redo_determinism: re-establish determinism for value-aware Step.
/-- Two results from the same start must be equal. SF original: `deterministic`;
`State ↔ X`, `relation ↔ R`, `start ↔ x`, `firstResult ↔ y₁`, `secondResult ↔ y₂`. -/
def Deterministic {State : Type u} (relation : State → State → Prop) : Prop :=
  ∀ start firstResult secondResult,
    relation start firstResult → relation start secondResult → firstResult = secondResult

/-- Every expression has at most one next small-step result. SF original:
`step_deterministic` in the `redo_determinism` exercise, using the value-aware `step`. -/
theorem stepDeterministic : Deterministic Step := by
  unfold Deterministic
  intros x y₁ y₂ h₁ h₂ -- beginning middle end


/-- Every expression is a value or can step. SF original: `strong_progress`;
`expression ↔ t`, `reducedExpression ↔ t'`. Optional practice on the chapter's theorem. -/
theorem strongProgress (expression : Expr) :
    Value expression ∨ ∃ reducedExpression, expression - -> reducedExpression := by
  sorry

/-- Concatenate two sequences of steps. SF original: `multi_trans`;
`State ↔ X`, `relation ↔ R`, `start ↔ x`, `intermediate ↔ y`, `finish ↔ z`.
`firstSteps`/`remainingSteps` correspond to `G`/`H` in the chapter's proof.
This is optional practice on the chapter's theorem. -/
theorem multiTransitive {State : Type u} {relation : State → State → Prop}
    {start intermediate finish : State}
    (firstSteps : Multi relation start intermediate)
    (remainingSteps : Multi relation intermediate finish) :
    Multi relation start finish := by
  sorry

end Smallstep
