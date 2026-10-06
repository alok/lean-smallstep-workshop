import InversionTests

set_option linter.missingDocs true

/-!
Every named regression proof must avoid `sorryAx` and custom axioms. Core
heterogeneous equality elimination may use Lean's standard `propext` axiom.
-/

run_cmd do
  let env ← Lean.getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if (`InversionTests).isPrefixOf name then
      if let .thmInfo _ := info then
        let axioms ← Lean.collectAxioms name
        unless axioms.all (· == ``propext) do
          throwError "{name} depends on unexpected axioms: {axioms}"
        unless axioms.isEmpty do
          Lean.logInfo m!"{name}: {axioms}"
        count := count + 1
  unless count == 32 do
    throwError "expected 32 named regression proofs, checked {count}"
  Lean.logInfo m!"Checked {count} regression proofs: no sorryAx or custom axioms."
