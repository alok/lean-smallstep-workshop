import Lean
import Inversion
import Smallstep

set_option linter.missingDocs true

/-! Expected resource-exhaustion diagnostics; these commands intentionally fail. -/

open Smallstep

/--
error: (deterministic) timeout at `whnf`, maximum number of heartbeats (1) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
set_option tactic.inversion.maxHeartbeats 1 in
example (source target : Expr) (h : Step source target) : True := by
  inversion h
  all_goals trivial
