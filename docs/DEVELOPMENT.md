# Development policy

[CONTRIBUTING](../CONTRIBUTING.md) remains the authority for setup, general
authoring, incremental checks and dependency changes. This page owns the
candidate-specific authoring and admission workflow and the affected-check adapter.

## Mathematical trust

Claimed closed results require source correspondence, explicit hypotheses and
foundation inputs, no transitive `sorry`, and axiom dependencies limited to
`propext`, `Classical.choice`, and `Quot.sound`. Custom and native-computation
axioms cannot discharge a proof. Preserve production dependency boundaries and
identify the source, pinned toolchain/dependencies and successful build. Retain
the existing selected-origin transitive axiom audit in ordinary final validation;
reuse compatible unchanged evidence and check changed or uncovered closure.
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

`bash scripts/check.sh` is a thin launcher for the independently pinned
`lean-incremental-ci` package. Install that distribution or select its tooling
checkout explicitly with `LEAN_CI_TOOLING_ROOT=/absolute/path/to/aglib`. The
checkout supplies `ci/lean_ci`; it is independent of the mathematical Aglib pin
in `lakefile.toml`. No ambient sibling checkout or mutable branch supplies tooling.
The reviewed shared-tooling revision for this adapter and CI is
`2fa27fe14c4df3b0fd8bc02d3e80181ad7f1bf95`.

The local entry compares tracked and untracked source bytes with `HEAD`.
`--base REF` widens that comparison; `--base REF --head REF` selects a committed
comparison with its head checked out. `--source-only` runs generated-import,
layout, placeholder and selected Python checks without Lean or dependency setup.
Source enrollment and absent configuration candidates are observed before
selection. Global pin/configuration or checker changes still require the existing
explicit invalidation assessment; missing history or caches never imply full
scope. `--aglib-source PATH` retains the exact Git-object assessment of a changed
Aglib pin. `--plan PATH` verifies a previously selected scope against current
inputs. `--full` explicitly selects the full in-package scope; it does not
re-elaborate already-built tests or append an acceptance chain.

Both local and committed entries declare the same shared native recipe. It runs
basic source/no-placeholder checks, root dependency preparation, one incremental
root Lake graph for selected production modules and affected in-package tests,
and selected declaration/text-style batch lint. The graph includes only those
modules and the required lint runtimes; it does not unconditionally build the
`Quillen` facade. No normal invocation elaborates a selected compile-time test
twice. The shared runner owns execution and resource limits; existing remote
wrapper profiles and Aglib resource aliases pass through its runtime.

Routine checks, including full scope, never add separate downstream setup,
builds, lint or audits, kernel replay, inventory or negative-control chains.
The `QuillenTest` aggregate that imports the optional kernel audit is excluded
from native selection; excluding replay must not remove existing production
transitive axiom coverage. Client-only edits receive static source checks without a
root build. Independent mathematical review and writing acceptance remain governed
by their own contracts.

Native local checks require the pinned root dependencies in the prepared workspace.
They do not create or require a downstream `.lake` container or package link.
Missing root prerequisites stop with an actionable diagnostic. Source-only checks
create no cache directory.

The shared entry prints its evidence directory. Set `--state /absolute/scratch/path`
(or `LEAN_CI_STATE`) to retain it across retries; state, progress and exported
mappings live outside the source checkout. Repeat the same entry after repair:
Lake keeps valid artifacts and the shared progress store reuses checks with
matching source, imports, checker, generated program, runtime and environment.
`--progress PATH` may select an existing compatible progress store. Source/style
checks explicitly bind their complete input boundary. Changed inputs invalidate
the affected evidence; local success remains working-tree evidence.
`scope.json` and the generated selected lint program are retained with native
invocations. Their presence records preparation, not successful lint coverage.
Direct scoped repair commands in
[CONTRIBUTING](../CONTRIBUTING.md#tests-and-checks) remain available.

CI uses the shared `EvidenceProtocol` to select an actual successful native
ancestor from exact reviewed workflow/recipe identities. It never uses
`event.before`, a previous push, or a full-build fallback. A requested comparison
may only widen that verified ancestor. Exact old/new Aglib source objects are
acquired before pin assessment when needed. The source and native phases consume
the same plan, require clean committed HEAD and bind the independently pinned
tooling implementation. Finalization reconstructs every required task and receipt
before native publication. Root mappings retain their workspace
identity and native JSONL format; exporting them never rebuilds targets.

A newly authored workflow/recipe is not admitted as successful historical evidence
merely by generating its own hashes. Its source identity requires actual owner
review. Historical receipts retain their original policy and source meaning.
