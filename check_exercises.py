#!/usr/bin/env python3
"""Check saved Lean exercises without editing the live files or editor buffers."""

from __future__ import annotations

import argparse
import subprocess
from collections.abc import Sequence
from pathlib import Path

PROJECT: Path = Path(__file__).resolve().parent
ARTIFACTS: Path = PROJECT / ".lake" / "build" / "lib" / "lean"
SCRATCH: Path = PROJECT / ".lake" / "checks"


def run(command: Sequence[str]) -> subprocess.CompletedProcess[str]:
    """Run one bounded local command, collecting its diagnostics."""
    return subprocess.run(
        list(command), cwd=PROJECT, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, timeout=60, check=False,
    )


def compile_module(source: Path, module: str) -> subprocess.CompletedProcess[str]:
    """Compile an isolated source snapshot into the project's ignored build folder."""
    return run([
        "lake", "env", "lean", f"--root={source.parent}",
        "-o", str(ARTIFACTS / f"{module}.olean"), str(source),
    ])


def prepare() -> bool:
    """Build the core and checker with warnings treated as failures."""
    result = run(["lake", "--wfail", "build"])
    if result.returncode:
        print(result.stdout, end="")
        return False
    ARTIFACTS.mkdir(parents=True, exist_ok=True)
    SCRATCH.mkdir(parents=True, exist_ok=True)
    result = run([
        "lake", "env", "lean", "-DwarningAsError=true", "-o",
        str(ARTIFACTS / "SmallstepGrader.olean"), "SmallstepGrader.lean",
    ])
    if result.returncode:
        print(result.stdout, end="")
        return False
    result = run(["lake", "env", "lean", "CoreChecks.lean"])
    print(result.stdout, end="")
    return result.returncode == 0


def self_test() -> int:
    """Verify rejection of direct/indirect holes, added axioms, and changed types."""
    controls = SCRATCH / "SmallstepGraderControls.lean"
    controls.write_text("""namespace GraderControls
theorem unfinishedDirect : True := by sorry
private theorem unfinishedHelper : True := by sorry
theorem unfinishedIndirect : True := unfinishedHelper
axiom extraAssumption : True
theorem usesExtraAssumption : True := extraAssumption
theorem wrongType : True := True.intro
end GraderControls
""", encoding="utf-8")
    result = compile_module(controls, "SmallstepGraderControls")
    if result.returncode:
        print(result.stdout, end="")
        return 1
    checks = SCRATCH / "NegativeChecks.lean"
    checks.write_text("""import SmallstepGraderControls
import SmallstepGrader
#check_proof GraderControls.unfinishedDirect : True
#check_proof GraderControls.unfinishedIndirect : True
#check_proof GraderControls.usesExtraAssumption : True
#check_proof GraderControls.wrongType : False
""", encoding="utf-8")
    result = run(["lake", "env", "lean", str(checks)])
    expected = (
        "FAIL GraderControls.unfinishedDirect: forbidden axioms [sorryAx]",
        "FAIL GraderControls.unfinishedIndirect: forbidden axioms [sorryAx]",
        "FAIL GraderControls.usesExtraAssumption: forbidden axioms [GraderControls.extraAssumption]",
        "FAIL GraderControls.wrongType: theorem type does not match",
    )
    if result.returncode == 0 or any(message not in result.stdout for message in expected):
        print(result.stdout, end="")
        print("FAIL checker controls: an invalid proof was not rejected as expected")
        return 1
    print("PASS checker controls: direct/indirect sorry, extra axioms, and changed types rejected")
    return 0


def check_saved_exercises() -> int:
    """Check a snapshot of the current saved exercise file; never save the editor buffer."""
    source = PROJECT / "SmallstepExercises.lean"
    saved = source.read_bytes()
    snapshot = SCRATCH / "SmallstepExercises.lean"
    snapshot.write_bytes(saved)
    result = compile_module(snapshot, "SmallstepExercises")
    if result.returncode:
        print(result.stdout, end="")
        return 1
    print("Checking the saved SmallstepExercises.lean snapshot (unsaved editor changes are excluded).")
    result = run(["lake", "env", "lean", "SmallstepChecks.lean"])
    print(result.stdout, end="")
    if source.read_bytes() != saved:
        print("The saved exercise file changed during checking; rerun to check the latest version.")
        return 1
    if result.returncode:
        print("Exercises are not all complete. FAIL reports do not change your proofs.")
    return 0 if result.returncode == 0 else 1


def main() -> int:
    """Run either checker controls or the saved exercises, after checking the trusted core."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true", help="test the checker without grading exercises")
    args = parser.parse_args()
    try:
        if not prepare():
            return 1
        return self_test() if args.self_test else check_saved_exercises()
    except subprocess.TimeoutExpired:
        print("A check exceeded 60 seconds; no exercise file was changed.")
        return 1
    except (OSError, UnicodeError) as error:
        print(f"Could not run the local checker: {error}")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
