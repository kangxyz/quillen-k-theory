# Contributing

Contributions should provide reusable mathematical definitions, proofs, or
interfaces. Keep hypotheses explicit and follow the conventions of
[mathlib](https://leanprover-community.github.io/contribute/style.html).
The [architecture](docs/development/Architecture.md) describes the current mathematical
owners; [scope](docs/reference/Scope.md) records the remaining comparisons.

## Adding mathematics

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

For iteration, build the changed module and its relevant clients:

```sh
lake build Quillen.KTheory.API
```

Run the complete pipeline before handing back a release candidate:

```sh
bash scripts/check.sh --rehash
```

The pipeline checks generated imports, module boundaries, placeholders, and
script tests; builds the library and maintained tests; runs `lake test`,
Batteries environment lint, and native mathlib text lint; then builds the
downstream package and explicitly replays both axiom audits. Library compilation
uses `autoImplicit = false`, the mathlib standard linter set, and warnings as
errors. The allowed foundation axioms are `propext`, `Classical.choice`, and
`Quot.sound`; see [the audit boundary](docs/development/Architecture.md#trust-checks).

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
[Performance.md](docs/development/Performance.md).

## API evolution

Reuse existing objects and canonical maps when extending a model. Give distinct
constructions distinct interfaces and state exact hypotheses for comparisons.
Module paths and declaration namespaces should reflect mathematical ownership.
Use one canonical interface for each construction, with minimal necessary
hypotheses and mathlib naming conventions. Update the
[API reference](docs/reference/API.md) when imports or interfaces change.

The library uses `0.x` versions. Breaking import or API changes require a minor
version bump and concise release notes; compatible corrections use patch
releases. Consumers should pin a release tag or commit. Update
[scope](docs/reference/Scope.md) when mathematical coverage changes and the
relevant [topic guide](docs/README.md#mathematical-topics) when its objects,
theorem inputs, canonical maps, or comparison boundary change.

## Documentation

The [documentation map](docs/README.md) owns topic navigation. Mathematical
guides live in `docs/topics/`, the shared API and scope references in
`docs/reference/`, and architecture and measured performance in
`docs/development/`. Extend the natural owner rather than duplicating a chapter
or adding a topic without existing mathematics and a reader.

Describe actual objects before their comparisons. Link focused Lean modules
and existing client proofs, retain all named data and hypotheses, and distinguish
positive-degree equivalences from degree-zero image or tail statements. A
constructed interface with conditional inputs does not realize those inputs
for every proposed application. Keep open comparisons in the relevant guide
and the cross-topic scope reference.

After moving documentation, update its internal links and the documentation
map. Check local paths and heading fragments, and compile any new Lean examples
against the pinned package. Documentation-only changes preserve existing proof
build evidence when source, dependencies, and runtime are unchanged.

## Dependency updates

Ordinary checks use the committed toolchain and manifests. Run `lake update`
when resolving a new consumer dependency or intentionally changing dependency
pins. For an upgrade, update the root and downstream toolchains and manifests
together, obtain the matching cache, and run the full pipeline. Explain affected
interfaces and theorem hypotheses.

Contributions are licensed under Apache-2.0.
