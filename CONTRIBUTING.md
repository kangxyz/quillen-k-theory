# Contributing

Contributions should provide reusable mathematical definitions, proofs, or
interfaces. Keep hypotheses explicit and follow the conventions of
[mathlib](https://leanprover-community.github.io/contribute/style.html).
The [architecture](docs/ARCHITECTURE.md) describes the current mathematical
owners; [scope](docs/SCOPE.md) records the remaining comparisons.

## Adding mathematics

New general theory intended for Aglib belongs in the
[local candidate source tree](Quillen/Aglib/README.md). Follow the
[candidate authoring policy](docs/DEVELOPMENT.md#aglib-candidates) for admission.
Its native namespaces and general dependency closure prepare a later upstream
move; application adapters keep their ordinary Quillen owners.

Place source in the nearest mathematical owner under `Quillen/`. Add a subject
or subdirectory when it has actual source and a useful consumer. Split modules
by mathematical objects or reusable interfaces; comparisons should depend on
the foundations they compare. Avoid empty future directories and inventories
that duplicate the source graph.

Follow nearby library files for Lean's module system: `module`, explicit public
imports where required by exported declarations, and an exposed public section.
Include an English module docstring describing the objects, main declarations,
assumptions, and references. New files carry author and Apache-2.0 headers.
List the actual contributors in the initial copyright header's comma-separated
`Authors:` field. When contributing to an existing implementation or test file,
append your name without replacing earlier credits.
Use English for maintained identifiers, comments, and documentation.

Implementation modules import their precise dependencies. Whole-topic and
whole-library facades serve clients. Importing a broad facade from an
implementation can create a cycle or an unnecessary dependency closure.
Library source must not import `QuillenTest`, tools, or downstream clients.

Use `attribute [local instance] ...` to enable an existing canonical structure
locally. Repeated anonymous local instances in sibling modules can generate
the same declaration name and break aggregate imports. Validate the affected
aggregate import when adding or changing instance declarations.

After adding or moving modules, regenerate imports:

```sh
python3 scripts/generate_imports.py
```

The generator discovers existing source modules and top-level subjects. It
preserves hand-maintained facades and enrolls existing nested facades only when
they carry the generator ownership marker. It does not require a fixed subject
list or create an empty hierarchy of possible future topics.
Each generated facade's `Authors:` list credits the contributors named in its
enrolled hand-owned sources, deduplicated and sorted deterministically. Family
facades use sources under their directory, the library root uses all production
sources, and the test root uses hand-owned tests. Generated facade headers do
not supply credits to other facades; a surface with no known source authors
retains the neutral team fallback. Regeneration preserves hand-owned headers.

Keep incomplete proofs and temporary probes outside the library and maintained
tests. State a genuinely conditional theorem with its actual hypothesis;
placeholders and new axioms do not discharge a missing proof.

## Tests and checks

Use `QuillenTest/` for interface, mathematical-property, and regression tests.
Use `examples/downstream/Consumer/` for client proofs compiled in a separate Lake
package. Choose a meaningful property or public use rather than a list of
names or a test that merely repeats its implementation.

Normal authoring, maintenance, documentation, review, merge, integration, and
release must use incremental checks and reuse trusted build artifacts and
compatible validation evidence. Reconcile the combined changes,
then build only changed or missing required leaf modules and their affected
consumers. The normal local and CI adapter selects the reverse import closure:

```sh
bash scripts/check.sh
bash scripts/check.sh --base BASE_COMMIT --head HEAD
```

The first command compares tracked and untracked local sources with `HEAD`;
the second compares the specified committed snapshots. Run the second command
with its selected head checked out. Documentation and documentation-evidence
JSON changes run static checks without Lean or cache work. See the
[scope adapter](docs/DEVELOPMENT.md#affected-check-scope) for ordering, cache
publication and unavailable-input behavior. For an explicit leaf while developing:

```sh
lake build Quillen.KTheory.API
```

Incremental validation also covers the applicable environment and text linters
and relevant tests. Normal incremental checks lint only added or modified local
source modules, while compilation still covers affected providers, tests and
clients and both trust audits retain their full selected coverage. Unmodified dependent modules remain in the build and test scope. Changed
import-only facades retain their existing native text checks. Explicit
comprehensive diagnostics and an initial baseline still lint all selected
modules. During the task's final validation, after building the changed
defining modules, run CI's default environment and native text linters on those
modules with:

```sh
lake env lean --run Tools/LintScoped.lean Quillen.KTheory.API
```

Pass additional defining module names as needed. The scoped runner includes
the slow default checks and generated declarations; it reads existing artifacts
without starting builds. Reuse compatible lint and test coverage outside the
affected scope, and run the relevant tests for the changed inputs.

After a final-check repair, resume the failed module or category and retain
completed provider checks. For the same selected scope, use the module names
and existing verification directory from the failed command. For example:

```sh
# Provider lint repair: compile the repaired source, then rerun its scoped lint.
lake build Quillen.KTheory.API
lake env lean --run .lake/verification/RUN/LintScoped.lean Quillen.KTheory.API
# A late test failure: compile and lint just that selected test.
lake build QuillenTest.ActionTranslationNaturality
lake env lean --run .lake/verification/RUN/LintScoped.lean QuillenTest.ActionTranslationNaturality
# A late client failure, from examples/downstream:
cd examples/downstream
lake build Consumer.AffineClosed
lake env lean --run ../../.lake/verification/RUN/LintScoped.lean Consumer.AffineClosed
# Rerun each failed or unrun audit chunk prepared for this scope.
lake env lean ../../.lake/verification/RUN/client-audit-0.lean
```

Replace `RUN` and the examples with the actual selected paths and modules.
Multi-batch client audits are prepared as `client-audit-N.lean`; a single batch
uses `client-audit.lean`. Replay only failed or unrun chunks, retaining completed
compatible checks. Complete any still-affected trust/client checks from the existing selected
commands; reselect when the import closure changes. The isolated lint runner
also handles import-only facades and tests without named declarations.

A merge, commit, branch switch, checkout, version bump, or publication does not
by itself require a whole-target build, fresh dependency replay, full audit, or
Python/source suite. Complete release coverage may combine compatible existing
evidence with new checks of the affected scope, including trust checks when
their inputs or coverage changed. Record the inputs and closure that each
piece of evidence covers.

Preserve caches. A missing artifact or receipt, or a different checkout, first
calls for matching available artifacts and evidence. Compile the missing
required closure only after checking for a usable matching cache. Toolchain,
dependency-pin, and global-option changes require matching caches and an
assessment of actual invalidation; they do not automatically assign a complete
library recompile. Missing coverage calls for checks of the uncovered affected
scope, not a blanket rebuild. Whole-library rebuilding is fault recovery outside
the normal workflow: diagnose incompatible, corrupt, or untrustworthy artifacts
throughout that closure and the absence of a usable matching cache first. A user
may explicitly request a literal full rebuild or replay; honor its exact scope
without assuming broader work.

The complete pipeline below remains available for explicitly requested comprehensive
diagnostics. It is not a normal local acceptance step
and does not itself request a clean rebuild:

```sh
bash scripts/check.sh --full --rehash
```

The pipeline checks generated imports, module boundaries, placeholders, and
script tests; compiles and lints production modules in dependency layers before
maintained tests and downstream clients. It replays test assertions and both
axiom audits, and includes Batteries environment lint and native mathlib text
lint. Normal CI uses the selected scope rather than this diagnostic scope. Library compilation
uses `autoImplicit = false`, the mathlib standard linter set, and warnings as
errors. The allowed foundation axioms are `propext`, `Classical.choice`, and
`Quot.sound`; see [the audit boundary](docs/ARCHITECTURE.md#trust-checks).

## Typechecking performance

Measure a fixed module before changing proofs or import structure. Use the
pinned Lean compiler and retain the selected source's actual build-command
`LEAN_PATH`, matching `--setup` JSON, and options. Redirect its `-o`, `-i`, and
`-c` outputs to fresh scratch paths. Add these supported profiling options:

```text
-j1 --profile -Dprofiler.threshold=10
-Dtrace.profiler=true -Dtrace.profiler.threshold=10
-Dtrace.profiler.output=/absolute/scratch/module.profile.json
-Dtrace.profiler.output.pp=true
```

`--profile` reports definition/theorem elaboration and checking times; the trace
export gives nested frames in Firefox profile format. Thresholds are in
milliseconds. Keep the command, source and dependency identities, exit status,
and logs with the measurement. A thresholded trace omits smaller frames;
frontend remainder also includes imports and untraced work. Inclusive frame
weights overlap and should not be summed or labelled whole-module CPU time.

Use profiles to select a bounded change, then compare matched unprofiled runs
with the same threads, options, outputs, and cache treatment. Alternate variants
and record durations; profiling overhead is not a production speed comparison.
Current measurements and their scope are recorded in
[Performance.md](docs/PERFORMANCE.md).

## API evolution

Reuse existing objects and canonical maps when extending a model. Give distinct
constructions distinct interfaces and state exact hypotheses for comparisons.
Module paths and declaration namespaces should reflect mathematical ownership.
Use one canonical interface for each construction, with minimal necessary
hypotheses and mathlib naming conventions. Update the relevant source-family README or focused mathematical/API guide
when imports or interfaces change. Use the [source-family index](Quillen/README.md)
to locate that authority, preserving hypotheses and canonical maps.

The library uses `0.x` versions. Breaking import or API changes require a minor
version bump and concise release notes; compatible corrections use patch
releases. Consumers should pin a release tag or commit. Update
[scope](docs/SCOPE.md) when mathematical coverage changes and the
relevant source-family guide linked by the [source-family index](Quillen/README.md) when its objects,
theorem inputs, canonical maps, or comparison boundary change.

## Documentation

The [documentation map](docs/README.md) owns package-wide navigation. Global
`docs/` owns navigation, cross-family scope, architecture, measured performance,
compatibility/history, source/runtime evidence, provenance and workflow.
Candidate-specific authoring is in [development policy](docs/DEVELOPMENT.md#aglib-candidates);
this contributor guide remains the setup, general authoring and check authority.
Mathematical content and current API/interfaces live in their occupied source
families under `Quillen/`, in a README or focused guide
linked from it. Reuse the natural owner; do not duplicate a mathematical chapter
or create empty future structure. Retain the existing `docs/` spelling.

Describe actual objects before comparisons. Link focused Lean modules and
existing client proofs; retain named data, hypotheses, canonical maps, degrees,
universes, source identities and citation locators. Distinguish proved results,
conditional interfaces and open comparisons. Keep each boundary with its family;
the global scope summary links to it. A constructed interface does not supply
its unresolved application inputs.

Convert completed proof plans into current proof/interface exposition where
they retain maintained value. Preserve useful source locators and evidence
boundaries; omit obsolete dispatch/phase chronology explicitly rather than
copying it wholesale into source guides.

After moving documentation, update internal and inbound links, heading fragments
and the documentation map, including references and footnotes after splits.
Compile new or modified Lean examples against the pinned package. A text-only
move preserves compatible proof build evidence when Lean sources, dependencies
and runtime are unchanged; it does not request a full rebuild or audit replay.

## Dependency updates

General interfaces already provided by Aglib use direct imports of precise Aglib
leaves and their native declaration names. Keep Q/K/G application constructions
in Quillen. Do not copy transferred implementations or restore their old module
aliases. Preserve weaker quasicoherent interfaces instead of adding Noetherian
hypotheses to fit a coherent specialization.

Ordinary checks use the committed toolchain and manifests. Run `lake update`
when resolving a new consumer dependency or intentionally changing dependency
pins. For an upgrade, update the root and downstream toolchains and manifests
together, obtain matching caches, and validate the actually affected modules,
consumers, and trust boundary using compatible prior evidence where applicable.
Explain affected interfaces and theorem hypotheses. A pin or toolchain change
alone does not require fresh compilation of unaffected libraries; normal local
acceptance remains incremental.

For the narrowly supported Aglib-only revision transition, select with
`python3 scripts/check_scope.py --aglib-source /absolute/path/to/aglib --output scope.json`.
The source path must be a real Git worktree root containing both exact pinned
commit objects; selection reads their blobs without network, Lean, or checkout
mutation. All three root/downstream pin owners must change together solely in
Aglib's `rev`/`inputRev`; other global changes still require separate assessment.
The selector recomputes old/new dependency closure and emits a portable assessment,
which the normal runner recomputes before accepting a plan:
`bash scripts/check.sh --aglib-source /absolute/path/to/aglib --plan scope.json`.
CI fetches exact source objects before selection and sets `QUILLEN_AGLIB_SOURCE`
for the source-only and execution consumers. An unchecked plan
is not a pin assessment. Actual runtime mathematical sources and configuration
must match the new pin; independently guarded runtime helper overlays confer no
exception to mathematical source drift.

Contributions are licensed under Apache-2.0.
