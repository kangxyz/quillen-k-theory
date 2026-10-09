# Contributing

Contributions should provide reusable mathematical definitions, proofs, or
interfaces. Keep theorem hypotheses explicit and use the conventions of
[mathlib](https://leanprover-community.github.io/contribute/style.html).

## Adding mathematics

Place source in `Quillen/<Subject>/<Topic>.lean`, extending the nearest existing
mathematical owner. New subjects can introduce new directories. Add a module
docstring describing the objects, main declarations, assumptions, and references.
Use English for maintained text and identifiers; identify authors and Apache-2.0
licensing in new file headers.

Implementation modules should import their precise dependencies. Whole-library
and whole-family entrypoints are intended for clients; importing them from an
implementation can introduce unnecessary dependencies or a cycle. Library code
must not import `Tests` or downstream clients.

After adding or moving modules, regenerate the import surfaces:

```sh
python3 scripts/generate_imports.py
```

The generator discovers the current source tree. It does not require a fixed
list of subjects or a source inventory. It preserves manually maintained
facades and updates generated files. `Quillen.Library`, `Quillen.Scheme`, and
`Quillen.Resolution` remain selected public entrypoints.

Keep incomplete proofs and development probes outside the library and its test
entrypoints. A theorem with an explicit hypothesis is a conditional result;
neither a placeholder nor an axiom is a substitute for the missing proof.

## Tests and checks

Use `Tests/` for maintained library tests and
`examples/downstream/Consumer/` for examples that exercise the public API from
another Lake package. Test an important property, interface, or regression;
temporary inspection programs and lists of declaration names do not belong in
the maintained test suite.

Run:

```sh
bash scripts/check.sh --rehash
```

This checks import generation and module boundaries, builds the library and
tests, compiles the downstream package, and replays the axiom audits. The allowed
foundation axioms are `propext`, `Classical.choice`, and `Quot.sound`.

For faster iteration, build the module being changed:

```sh
lake build Quillen.KTheory.API
```

## API evolution

Reuse a model's existing objects and canonical maps when extending it. Give
distinct constructions their own interfaces and state the hypotheses of
comparison theorems. Keep natural declaration namespaces even when source files
move. Document public import, namespace, or hypothesis changes for users.

The library currently uses `0.x` versions. Breaking changes require a minor
version bump and migration notes; compatible corrections use patch releases.
When practical, retain deprecated aliases or small compatibility modules for
one minor release. Consumers should pin a release tag or commit.

Update [Scope.md](docs/Scope.md) when the mathematical coverage changes, and the
[library guide](docs/Library.md) when public interfaces change.

## Dependency updates

Ordinary checks use the committed toolchain and manifests. Do not run
`lake update` merely to check a source change.

For an intentional upgrade, update the root and downstream toolchains and
manifests together, obtain the matching cache, and run the complete checks.
Explain any affected API or theorem hypotheses. Keep dependency upgrades separate
from unrelated mathematical changes when possible.

Contributions are licensed under Apache-2.0.
