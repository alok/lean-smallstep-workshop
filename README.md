# Smallstep in Lean 4

Follow [Software Foundations: Smallstep](https://softwarefoundations.cis.upenn.edu/plf-current/Smallstep.html)
alongside this small companion. This covers the constants/addition language,
values, reduction rules, and multi-step reduction; later chapter material such
as Imp, concurrency, and stack machines is outside this starter's scope.

1. Read `Smallstep.lean` alongside “A Toy Language” and “Values”.
2. Inspect `leftStepExample` and `twoStepExample` in Lean's Infoview.
3. Work in `SmallstepExercises.lean`; its unfinished proofs are yours to complete.

This is a workshop snapshot. It preserves the saved proof progress, including
an incomplete determinism proof, alongside explicit exercise holes. No exercise
solutions have been added. The core and its worked examples build independently
of the exercise file.

The first two exercises correspond to the chapter's `test_step_2` and
`redo_determinism`. The last two are optional practice on chapter theorems.

Lean uses descriptive names: `Expr.constant`, `Expr.add`, `evaluate`,
`Step.addConstants`, `Step.stepLeft`, and `Step.stepRight`. Variables such as
`left`, `right`, and `reducedLeft` say what each expression does. Original SF
names remain in comments and the quick map at the end of `Smallstep.lean`.

Both Lean files enable `linter.missingDocs`. Public declarations, constructors,
reduction notation, and exercise statements have doc comments for hover help.
Each comment gives its original SF/Rocq name and relevant parameter mappings,
including `relation ↔ R`, `State ↔ X`, and `expression ↔ t`. Helpers introduced
for this companion are marked Lean-only.

## Check your work

Install [Lean with elan](https://lean-lang.org/install/) if needed, then clone
and open the project:

```sh
git clone https://github.com/alok/lean-smallstep-workshop.git
cd lean-smallstep-workshop
```

The project pins `leanprover/lean4:v4.34.1`. Elan downloads that toolchain if it
is not already installed. Python 3 is needed only for the checker. There are no
Mathlib or other package dependencies.

Open a terminal in this folder:

```sh
lake build
lake env lean SmallstepExercises.lean
```

`lake build` checks the core, worked examples, and inversion regressions. The second command checks
the saved exercise file. Unfinished tactic proofs can report unsolved goals;
each remaining `sorry` produces a warning. A file accepted with those warnings
does not prove the exercises.

## Check completed exercise proofs

This companion includes an **unofficial Lean-only checker**, separate from
Software Foundations' Rocq grading files. Save your exercise file, then run:

```sh
python3 check_exercises.py
```

The checker reports PASS or FAIL for each exercise. It checks the expected
theorem type and every axiom used transitively by its proof. A `sorry` hidden
inside a helper theorem also fails. Lean's standard `propext`, `Classical.choice`,
and `Quot.sound` are allowed; additional axioms are rejected. The completed
core examples are checked first, and the core build treats warnings as errors.

Exit status 0 means all four exercises passed. Exit status 1 means a check failed
or work remains unfinished. This snapshot intentionally has unfinished work,
so the exercise check is expected to exit with status 1.
This is proof checking, not an official SF score or a guarantee against changes
to the language definitions in the core file.

Checks use a snapshot of the **saved** exercise file. Unsaved editor changes are
excluded; the checker never edits your proof file or saves the editor buffer.
If you save another version during checking, it asks you to rerun.

To test the checker itself without grading exercises:

```sh
python3 check_exercises.py --self-test
```

The controls verify that trusted worked proofs pass and direct/indirect holes,
added axioms, and changed theorem statements fail. The control files are created
only under the ignored `.lake` build folder and contain no exercise solutions.

## Rocq-style inversion

The exercise file imports the dependency-free workshop tactic from
`Inversion.lean` (version 0.3.0). Use `inversion h`, `inversion h as [...]`,
or `inversion_clear h`, and inspect the resulting cases in the Infoview.
Ordinary inversion retains the original proof and useful index equations;
`inversion h; subst_vars` requests substitution explicitly.

The behavior for this companion's `Value` and `Step` relations was compared
with Rocq 9.3.0. Names and hypothesis order can differ. See
[Inversion.md](Inversion.md) for naming syntax, supported behavior, limits,
and the remaining differences from Rocq.

`lake build` also checks 32 inversion regressions, negative/rollback checks,
resource limits, and their axiom audit. Those checks use the actual core
module and contain no completed workshop exercise proofs. The grader's
positive controls include a proof produced by inversion.

## Cursor and notation

Use the installed `leanprover.lean4` extension. Open the Command Palette with
Cmd+Shift+P and run **Lean 4: Toggle Infoview** if the pane is closed. Place the
cursor on a `sorry` or after a tactic to inspect the goal.

- `t - -> u` is one semantic step; `t - ->* u` is zero or more steps.
- `t = u` is equality. Use `rw [h]` for an equality proof and `rw [← h]` backwards.
- For reduction proofs, use the `Step` constructors; reduction is not equality.
- SF writes `-->` and `-->*`. Lean reads adjacent `--` as a line comment, so
  use `- ->` and `- ->*` with the space between hyphens. The earlier Unicode
  spellings remain compatible aliases. You can copy the symbols from the existing statements. The Lean
  extension also supports `\to` for `→`, `\leftarrow` for `←`, and `\_s` for `ₛ`.

## Source and license

This Lean companion adapts the toy arithmetic and value-aware reduction material
from [Software Foundations, Volume 2: Programming Language Foundations,
Smallstep](https://softwarefoundations.cis.upenn.edu/plf-current/Smallstep.html),
version 7.1 (2026-08-24). The authors are Benjamin C. Pierce, Arthur Azevedo de
Amorim, Chris Casinghino, Marco Gaboardi, Michael Greenberg, Cătălin Hriţcu,
Vilhelm Sjöberg, Andrew Tolmach, and Brent Yorgey.

The translation uses descriptive Lean names, SF-style notation, hover comments
mapping SF/Rocq names and parameters, and a local proof checker. It is an
unofficial follow-along project, not an official SF translation or grader.
It covers a small part of the chapter rather than the entire book.

Distributed under the MIT license. [LICENSE](LICENSE) preserves the upstream
copyright and permission notice from the
[official PLF license](https://softwarefoundations.cis.upenn.edu/plf-current/LICENSE).
