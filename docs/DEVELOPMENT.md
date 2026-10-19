# Development policy

[CONTRIBUTING](../CONTRIBUTING.md) remains the authority for setup, general
authoring, incremental checks and dependency changes. This page owns the
candidate-specific authoring and admission workflow and the affected-check adapter.

## Aglib candidates

The [`Quillen/Aglib/` source tree](../Quillen/Aglib/README.md) holds maintained
general-theory source developed in Quillen for later inclusion in Aglib. Follow the [shared candidate policy](https://github.com/kangxyz/aglib/blob/main/doc/DEVELOPMENT.md#downstream-candidates-for-aglib).

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

`bash scripts/check.sh` compares local Lean sources with `HEAD`. Use `--base REF
--head REF` for a committed comparison, with the head checked out. `--source-only`
runs generated-import, layout, placeholder and Python tooling checks without
Lean. All normal invocations keep existing artifacts; `--rehash` checks Lake
traces without cleaning. `--full` is an explicit comprehensive diagnostic scope
and is never inferred from missing cache data, missing Git history, pins or an
unclassified path. CI fetches complete comparison history and exposes a default
false `workflow_dispatch` full-scope input; a normal dispatch compares `HEAD^`.
A zero-before new branch recovers the default-branch merge base when it provides
an independent comparison. A true initial commit uses `--base EMPTY_TREE`, with
all added sources as its actual changed scope. Missing or tautological comparison
bases stop with an actionable error.

The selector reads both old and current import graphs, so renamed/deleted modules
still select their surviving consumers. Changed providers compile in dependency
layers, and each layer passes the existing default scoped environment and native
text checks before affected dependent layers, tests or clients compile. The
`QuillenTest` driver is a Lean library: compiling its selected modules executes
their compile-time assertions, and compatible cached test artifacts retain that
coverage. Normal checks do not elaborate the same test sources a second time;
explicit `--full` diagnostics replay the selected test sources. Separate axiom
audits retain their explicit replay. Test-only edits select test
targets without requesting producer builds; Lake may recover a genuinely missing
import artifact. Unchanged import-only facades are not blanket build targets.
Changed facades compile and receive text checks; actual tests or clients that
import a broad facade retain that real import closure. In particular, the public
library clients can require the cached complete library as their import basis.
Missing compatible artifacts may require that actual dependency closure; the
selector never substitutes unrelated roots.

The existing axiom-audit bodies are copied into the verification directory with
only their import list scoped to the selected production/client modules. Their
origin predicate, checked-kernel requirement and allowed axioms remain unchanged.
An audit-body change selects the complete corresponding trust surface because
that body governs it. The scoped linter copy permits an empty defining-declaration
set for import-only facades while retaining all environment and native text
checks. Production, test and client coverage is recorded separately in
`.lake/verification/.../scope.json`; a partial plan does not claim whole-library
coverage. Global toolchain, manifest, Lake-option, exclusion or Lean-checker
changes stop for an explicit invalidation/scope assessment.

CI computes scope before installing Lean or restoring dependencies. Pure Markdown
and `docs/` evidence changes perform only static checks and skip cache checkout,
restore, export and publication. Relevant compilation uses the already pinned
Aglib `build_serial.py` cache probe and resource guard. Dependency proof-cache
fetches follow only the selected source imports and the scoped linter runtime.
The linter's exact Batteries/Mathlib imports receive incremental guarded tooling
preparation when needed; this does not request a project-root build. Every selected build writes
native mappings via that existing helper's `--outputs` argument. Only after all
selected lint, test and trust checks succeed are those same mappings combined for
publication; export does not invoke another build or introduce wider targets.
`--plan PATH` consumes the CI selector's JSON and rejects changed scope inputs.
`--source-checked` reuses the preceding successful static check on the same inputs.
`--ci --native-outputs PATH` writes verified mappings; it requires resolved pinned
Aglib tooling. Fresh verification directories prevent overwriting earlier evidence.
CI prints only recorded operational receipt fields and their exact locators;
complete receipts and probe logs are retained in the run's
`quillen-check-receipts-RUN_ID-RUN_ATTEMPT` artifact. These process summaries do
not certify proof coverage or supply unrecorded compiler counts.
