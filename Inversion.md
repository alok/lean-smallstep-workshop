# Lean workshop inversion

Version **0.3.0** provides `inversion h`, `inversion h as [...]`, and
`inversion_clear h` for Lean **4.34.1**, without external dependencies.
It follows ordinary Rocq inversion for the Smallstep `Value` and `Step`
relations: keep the original proof and indices, split into constructor cases,
eliminate incompatible constructors, inject equal constructors, retain useful
index equations, and rewrite newly derived rule premises.

```lean
import Smallstep
import Inversion

open Smallstep Smallstep.Expr

example (expression : Expr) (h : Value expression) :
    ∃ n, expression = constant n := by
  inversion h as [n E]
  -- h : Value expression
  -- E : constant n = expression
  exact ⟨n, E.symm⟩
```

After `inversion h`, inspect the Infoview. For surviving `Step` rules use
`case addConstants`, `case stepLeft`, and `case stepRight`. Names supplied by
`as` include implicit constructor arguments, then ordinary rule premises, then
one equation for each relation index. Separate all constructor branches by
`|`, including those which turn out to be impossible:

```lean
inversion h as
  [n m Es Et | left reduced right premise Es Et |
   left right reduced valuePremise stepPremise Es Et]
```

Each injected equation gives its requested name to its first component; further
components receive fresh `H0`, `H1`, … names. An underscore requests an automatic
name. Without `as`, constructor fields have Lean's usual inaccessible names,
which `case` or `rename_i` can expose.

`inversion h; subst_vars` corresponds to the common Rocq sequence
`inversion H; subst`. Substitution is explicit because ordinary inversion keeps
useful equations. `inversion_clear h` rewrites existing proof hypotheses and the
goal, clears the original proof and generated equations, and removes unused
constructor data. Rule premises remain available for a separately requested
inversion. The tactic acts on the focused goal; use `all_goals` when desired.

## Using the integrated tactic

`SmallstepExercises.lean` already imports `Inversion`. Run `lake build` to
check the core and all inversion regressions. The regression files import
`Smallstep.lean`; they never import or complete the exercise module.

Use `inversion Hy₂` where you would use Rocq's `inversion Hy2`. The focused
goal splits into constructor cases. Inspect the Infoview after the tactic,
then choose `case` or explicit `as` names. Keep `subst_vars` explicit when
you want substitution, as in Rocq's `inversion H; subst`.

## Rocq comparison and limits

`RocqProbe.v` contains deliberately aborted diagnostic goals, and
`RocqProofStates.txt` records their output from **Rocq 9.3.0**. They check
generic/concrete/partially fixed `Value` and `Step` indices, equality injection,
arithmetic index equations, clearing, and branch naming.
The Lean regression suite checks the corresponding proof-state properties.

For example, ordinary `Value` inversion retains
`h : Value t`, a witness `n`, and `E : constant n = t`.
Partially fixed `Step (add a b) result` inversion rewrites the left-step
premise to `Step a reduced`, and the right-step premises to
`Value a` and `Step b reduced`, retaining the original `h`.
Clearing the same relation removes index equations and unused witnesses while
keeping those rule premises. These behaviors agree with the Rocq probes.

This is a bounded workshop tactic, with these remaining differences:

- Automatic names, equation numbering, and hypothesis order can differ from
  Rocq. Use `as` for reliable ported names.
- Only named local proofs of inductive propositions are accepted. Arbitrary
  proof terms, data elimination, `using`, `in ...`, anonymous hypothesis
  selection, nested `as` patterns, and `dependent inversion` are unsupported.
- Arbitrary function-headed equations are retained; no function injectivity,
  arithmetic reasoning, or recursive premise inversion is attempted.
- General dependent index tuples and heterogeneous equality do not have the
  full Rocq implementation's behavior. Homogeneous `HEq` is supported when
  Lean core can convert it to equality; other heterogeneous equations can
  remain unresolved.
- `inversion_clear` fails transactionally if a dependent target or hypothesis
  still requires the original proof, or a required rewrite cannot eliminate a
  generated equation. It does not silently discard a dependent premise.

The defaults cap constructors at **32**, equality-processing steps per branch
at **256**, recursion depth at **256**, and work at **20000** Lean heartbeat
units. The smaller nonzero standard `maxRecDepth`/`maxHeartbeats` limits also
apply. The constructor count includes constructors whose indices later exclude
them. Options can be adjusted locally:

```lean
set_option tactic.inversion.maxConstructors 64 in
-- theorem or example here
```

The other options are `tactic.inversion.maxEquations`,
`tactic.inversion.maxRecDepth`, and `tactic.inversion.maxHeartbeats`;
all three must be positive. Exhaustion fails without an accepted partial proof.
Fresh automatic names also have a bounded search of 4096 candidates.

## Validation and implementation sources

The default build enables `linter.missingDocs` and treats warnings as errors.
There are **32 named regression proofs**, additional negative/rollback checks,
an actual heartbeat-exhaustion diagnostic check, and an audit rejecting
`sorryAx` or custom axioms. All 32 named proofs currently have empty axiom
dependency sets. The audit permits Lean's standard `propext` if core
heterogeneous elimination requires it in later tests.

`InversionTests.lean` checks the project's actual `Smallstep.lean` definitions.
No exercise module is imported.

Existing alternatives were checked before implementing the interface:

- Lean core's `cases`, `rcases`, `injection`, `injections`, and `subst_vars`.
  This implementation uses core `generalizeIndices`, `MVarId.cases`,
  `injectionCore`, and kernel-checked equality rewriting/replacement.
- Local mathlib `casesm`/`cases_type` add selection and repetition around
  `cases`; no standalone relation-inversion tactic was found in that tactic
  directory. Mathlib is unnecessary here.
- [Lean's inductive-type tutorial](https://lean-lang.org/theorem_proving_in_lean4/Inductive-Types/)
  explains constructor analysis and dependent context handling.
- [Rocq's inversion source](https://github.com/rocq-prover/rocq/blob/master/tactics/inv.ml)
  constructs a motive carrying index equations in `make_inv_predicate`, then
  processes them in `rewrite_equations`. The Lean tactic uses the same broad
  strategy with Lean's core proof-producing operations.
- [Rocq's inductive-reasoning reference](https://rocq-prover.org/doc/v9.0/refman/proofs/writing-proofs/reasoning-inductives.html)
  distinguishes ordinary, clearing, and dependent inversion.

Installed Lean core sources are under
`~/.elan/toolchains/leanprover--lean4---v4.34.1/src/lean/Lean/Meta/Tactic/`:
`Cases.lean`, `Injection.lean`, `Rewrite.lean`, `Replace.lean`, and
`FVarSubst.lean`.
