import Smallstep
import SmallstepGrader

/-! Lean-only positive controls: both completed worked examples must pass. -/

open Smallstep Smallstep.Expr

#check_proof Smallstep.leftStepExample :
  add (add (constant 1) (constant 3)) (add (constant 2) (constant 4)) - ->
  add (constant 4) (add (constant 2) (constant 4))

#check_proof Smallstep.twoStepExample :
  add (add (constant 1) (constant 3)) (constant 2) - ->* constant 6
