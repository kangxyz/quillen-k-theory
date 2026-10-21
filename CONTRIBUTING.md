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
python3 -m lean_ci imports --config .github/lean-ci.toml --root . --write
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
consumers. The common checker selects affected modules through the union of
old and new reverse-import graphs:

```sh
python3 -m lean_ci check --config .github/lean-ci.toml --root .
python3 -m lean_ci check --config .github/lean-ci.toml --root . --requested-base BASE_COMMIT
```

Use the shared tooling distribution selected by the reusable workflow, separately
from the mathematical Aglib dependency. The second command may widen selection
from a verified native ancestor; a previous push does not establish check coverage.
See [development policy](docs/DEVELOPMENT.md#affected-check-scope) for preparation,
coverage and recovery. During proof development, build a specific leaf:

```sh
lake build Quillen.KTheory.API
```

At final validation, the common profile covers applicable source organization,
placeholders, source style and budget checks; selected production compilation;
builtin and exact defining-origin declaration lint; selected `QuillenTest` modules;
the independent `Consumer` package; and selected-origin trust and axiom checks.
Selected compile-time tests execute through their Lake build. They are not replayed
as separate whole-test frontend commands. Import-only facades remain enrolled and
compiled; only a conservative declaration-free certificate can omit empty
declaration-lint work.

The shared declaration checker uses a fixed isolated environment for each origin:
`Batteries.Tactic.Lint` followed by that origin, private visibility and the pinned
native linter's options and trust setting. This predicate differs from the former
whole-library and target-first scoped lints; those older successes do not establish
its new declaration-lint obligations. Axiom checks retain their separate kernel
trust setting and include private and generated declarations. Allowed foundation
axioms are `propext`, `Classical.choice`, and `Quot.sound`; see
[the audit boundary](docs/ARCHITECTURE.md#trust-checks).

Keep the same external state and progress paths after a failure:

```sh
python3 -m lean_ci check --config .github/lean-ci.toml --root . \
  --state /absolute/scratch/quillen-state --progress /absolute/scratch/quillen-progress
```

The common runner retains compatible individual successes immediately. Repair the
failed input and repeat that entry; changed checker/source/import inputs invalidate
only affected evidence. Root and downstream modules keep their distinct package
coordinates. Source bytes, generated recovery programs, build artifacts and passed
checker receipts provide different evidence; warm artifacts alone do not prove a
checker passed.

A merge, commit, branch switch, checkout, version bump or publication does not by
itself request a whole-library build, fresh dependency replay or full audit. Preserve
matching artifacts and evidence. Missing coverage calls for currently uncovered
obligations. Toolchain and dependency changes require explicit old/new input and
import-graph assessment; they do not automatically invalidate every mathematical
output. Missing or failed history lookup must not silently become a complete build.

Whole-library rebuilding is exceptional fault recovery: first diagnose incompatible,
corrupt or untrustworthy artifacts throughout that closure and the absence of a
usable matching cache. A user may explicitly request a literal full rebuild or
replay; honor that exact scope without assuming broader work.

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

The common selector assesses changed dependency pins against exact old and new
source identities and their import graphs. Keep the source objects and matching
runtime dependencies available for that assessment. An unchecked plan or a warm
cache does not supply the assessment. Unknown global invalidation fails visibly;
it does not select a blanket rebuild. Runtime mathematical sources and configuration
must match the selected pins; a separate tooling pin provides no exception to
mathematical source drift.

Contributions are licensed under Apache-2.0.
