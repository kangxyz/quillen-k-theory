# Development policy

[CONTRIBUTING](../CONTRIBUTING.md) remains the authority for setup, general
authoring, incremental checks and dependency changes. This page owns the
candidate-specific authoring and the native local-check entry.

## Mathematical trust

Claimed closed results require source correspondence, explicit hypotheses and
foundation inputs, no transitive `sorry`, and axiom dependencies limited to
`propext`, `Classical.choice`, and `Quot.sound`. Custom and native-computation
axioms cannot discharge a proof. Preserve production dependency boundaries and
identify the source, pinned toolchain/dependencies and successful build. Retain
production transitive axiom coverage through the pinned upstream auditor in
ordinary native final validation; reuse compatible command evidence for unchanged closure.
Source token checks and ordinary lint do not supply transitive axiom coverage.
This is an existing mathematical trust predicate, not kernel replay or an added
acceptance stage. Independent mathematical review and writing acceptance retain
their governing requirements; conditional theorems retain their premises.

## Normal task

Use the prepared workspace: encode/prove, compile the exact changed leaf, and
repair from its diagnostics. For example:

```sh
lake build Quillen.KTheory.Functor
```

At meaningful final delivery, run the selected check once:
`bash scripts/check.sh --base ACCEPTED_COMMIT`. Use a consumer only for a concrete
interface question. After a failure, keep completed categories and use the
[direct scoped repair commands](../CONTRIBUTING.md#tests-and-checks). Consult
setup, dependency/cache or environment guidance only for an actual missing or
invalid input; preserve the prepared workspace and matching evidence.

## Aglib candidates

The [`Quillen/Aglib/` source tree](../Quillen/Aglib/README.md) holds maintained
general-theory source developed in Quillen for later inclusion in Aglib. Follow the [shared candidate policy](https://github.com/kangxyz/aglib/blob/main/docs/DEVELOPMENT.md#downstream-candidates-for-aglib).

Use `Quillen/Aglib/` as the source location and `Quillen.Aglib` as the temporary
module prefix. Mirror the intended Aglib mathematical path below it. Keep
native mathematical declaration namespaces, so migration normally changes
imports rather than the meaning or names of the interfaces. A package-root
`Aglib/` tree would shadow the upstream dependency and must not be used here.

Before adding a candidate, check existing Mathlib and Aglib APIs. Keep its
imports in Mathlib, Aglib, or explicitly designated general candidate leaves;
keep host applications and their adapters outside this subtree. Coordinate
one implementation owner across downstream libraries. Record the intended
upstream module, exact hypotheses and current consumer in the module docstring,
and describe interfaces and main results in each occupied family's README.

Candidates are enrolled and checked as ordinary Quillen production modules.
They are not scratch, a separate Lake library, or proof of upstream acceptance.
Once an accepted upstream revision is pinned, retarget the consumers and remove
the local implementation; avoid duplicate implementations and default legacy
facades.

Existing general-theory implementations are staged here before admission to
Aglib. Specialized applications remain in their mathematical host families and
import the focused candidate leaves. Mixed files separate their general
constructions from their curve, arithmetic or K-theory endpoints.

The candidate module prefix records the temporary implementation owner. Source
relocation preserves existing declaration names, objects, hypotheses and chosen
comparison maps; it does not by itself redesign the public mathematical API.
Future upstream admission selects canonical native namespaces and removes the
accepted local implementation together with its old imports.

## Affected check scope

[CONTRIBUTING](../CONTRIBUTING.md#tests-and-checks) owns the native local commands.
`scripts/check.sh` forwards through the thin `check_run.py` entry to the installed
shared `lean_ci.cli`, with `Quillen` as the explicit production root. Its
checkout package is `scripts/lean_ci`, installed from `scripts/pyproject.toml`. Set
`LEAN_CI_TOOLING_ROOT` only to select an explicit tooling checkout; no ambient
sibling, mathematical dependency pin or whole-package Git recipe hash selects
that executable. Existing installed older tool versions are separate installations.

Use `lake --rehash build +MODULE` during proof iteration. The final entry uses
CI's native production build, checker preparation, in-package `lake test`,
generated-entry check, text style, native lint and pinned upstream axiom audit.
A final whole-root command can still reuse all compatible native outputs; it is
not a clean rebuild. `--full` adds no replay, client or audit chain.

A nonempty docs-only comparison runs the retained source checks without Lean.
Clean/no-change checks remain native. `--source-only` records only static
coverage. `--list` displays commands without executing them. Use external
`--state`/`--receipt-dir`, `--progress` and `--outputs` paths where applicable.
Successful command reuse binds actual source/native/checker inputs and toolchain;
partial, failed or changed commands cannot supply a pass. Delivered native
mappings retain their compilation/recovery meaning and add no proof coverage.

Public CI uses the separately pinned shared native workflow and its existing
Build/Test/Publish split. Local checking has no GitHub baseline, committed-phase,
frozen-plan or recipe-admission lifecycle. Source and compiler success do not
establish mathematical correspondence. Retain the mathematical trust conditions
and independent review described above.
