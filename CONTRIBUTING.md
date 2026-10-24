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

Use `QuillenTest/` for mathematical-property, interface and regression tests.
Choose a meaningful public use, sign, universe or edge case. Production cannot
import tests, tools or independent downstream packages.

During proof iteration, build the changed module in the prepared workspace:

```sh
lake --rehash build +Quillen.KTheory.API
```

At final validation use the same native commands as public CI through the shared
entry:

```sh
bash scripts/check.sh
bash scripts/check.sh --base BASE_COMMIT --head HEAD
bash scripts/check.sh --source-only
bash scripts/check.sh --list
```

Install the current `lean-incremental-ci` package or explicitly select its Aglib
tooling checkout with `LEAN_CI_TOOLING_ROOT=/absolute/path/to/aglib`. Its
package lives at `scripts/lean_tools`; install from `/absolute/path/to/aglib/scripts`. This is
independent of the mathematical Aglib dependency. The entry forwards to
`lean_tools.cli.main`. Shared library data selects production root `Quillen`;
Source boundaries, placeholders and thematic imports use the same
`lean_tools.policy` and `lean_tools.imports` implementations as the other libraries.
Cache-root discovery and recovery use the common `lean_tools.cache` module.
The checkout retains only bootstrap wrappers for current commands. With the
toolkit installed, use `lean-tools check --root /path/to/quillen-k-theory` or
`lean-tools imports --root /path/to/quillen-k-theory` directly.

The final native graph uses `lake --rehash build Quillen`, preserving valid
Lake artifacts, then prepares native checker tools, runs `lake test`, checks
production entries with `mathlib/mk_all --lib Quillen --check`, and runs native
text style, `lake --no-build lint Quillen -- --trace` and the pinned upstream
production axiom auditor. Test libraries use `QuillenTest.+` globs; no generated
`QuillenTest.lean` is required. No explicit module list is passed to `lake test`:
its configured library driver accepts no arguments. The split `Quillen` and
`QuillenModules` libraries have empty `roots`; final commands always pass the
production root explicitly instead of relying on root inference.

`--base` and `--head` describe the source comparison, with the selected head
checked out. A nonempty documentation-only difference runs static checks without
Lean setup; a clean/no-change invocation still requests the native final check.
`--source-only` is explicit static coverage. `--full` uses the same incremental
native graph and predicates; it does not force recompilation, kernel replay,
separate clients or extra acceptance stages. Native Lake traces decide rebuilds.

Use external `--state`/`--receipt-dir` and `--progress` paths for diagnostics and
compatible per-command successes. After repair, repeat the same entry; only
changed or missing command evidence reruns. `--outputs PATH` delivers native
mappings from the selected successful build without another compilation. Those
mappings describe compilation, not mathematical correspondence or check success.

Source checks retain import direction, local-source existence, DAG, thematic
facade and placeholder checks. Mathlib owns production-root generation; the
Python generator owns only enrolled thematic facades and the explicit example
client facade. Text style reads production-root import lists, without a custom
injected checker. The upstream axiom auditor loads built production module
origins and enforces `propext`, `Classical.choice` and `Quot.sound`; it does not
replay proofs or claim source correspondence. Keep independent mathematical
review and writing acceptance under their governing requirements.

Cache setup is separate from ordinary checking. Recover matching pinned
artifacts before compiling missing required closure. `bash scripts/cache.sh
Quillen.KTheory.API` fetches explicit reachable Mathlib inputs; omit targets only
for an explicitly intended workspace cache setup. `--ci` runs the scoped
`lake exe cache get` through the installed toolkit's guarded `run --bootstrap-cache`;
it does not load tools from the mathematical dependency checkout. The entry does not update mathematical pins,
require downstream setup or use GitHub history as local acceptance.

## Typechecking performance

Keep the standard 200,000-heartbeat package default. A necessary finite
increase stays declaration-local with an adjacent explanation; restore the
standard budget when the retained repair permits it, and compile the affected
module. Selecting that allowance does not require profiling.

At a compilation bottleneck, use targeted diagnostics or profiling when existing
feedback cannot guide the next repair; no separate user approval is needed.
Start from the implicated declaration/module and its retained evidence. Ordinary
proof or import changes do not require measurement. For a profile, use the
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

For a speed comparison, use profiles to select a bounded change and
compare matched unprofiled runs with the same threads, options, outputs and cache
treatment. Profiling overhead is not a production speed comparison. These
procedures add no benchmark requirement to ordinary repair or finite-budget
selection.
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

Dependency changes require a mathematical assessment of the affected interfaces
and hypotheses. Obtain matching dependency caches, build the actual changed
leaves during iteration and run the native final entry on the integrated
snapshot. Local validation does not synthesize or admit an old/new pin scope
certificate. The root and any independently requested client keep their own
manifests and output ownership.

Contributions are licensed under Apache-2.0.
