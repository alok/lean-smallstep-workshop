import SmallstepExercises
import SmallstepGrader

/-!
Lean-only checks for the four companion exercises. These expected statements
are kept separate from the exercise file so changing a theorem's statement
does not silently make its check easier. No solutions are supplied here.
-/

open Smallstep Smallstep.Expr
universe u

#check_proof Smallstep.rightStepExercise :
  add (constant 0) (add (constant 2) (add (constant 1) (constant 3))) - ->
  add (constant 0) (add (constant 2) (constant 4))

#check_proof Smallstep.stepDeterministic :
  ∀ start firstResult secondResult : Expr,
    Step start firstResult → Step start secondResult → firstResult = secondResult

#check_proof Smallstep.strongProgress :
  ∀ expression : Expr, Value expression ∨ ∃ reducedExpression, expression - -> reducedExpression

#check_proof Smallstep.multiTransitive :
  ∀ {State : Type u} {relation : State → State → Prop}
    {start intermediate finish : State},
    Multi relation start intermediate → Multi relation intermediate finish →
    Multi relation start finish
