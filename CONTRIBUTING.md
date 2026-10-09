# Contributing

This library is under active development. Extend the mathematics at its natural
object owner, keep hypotheses visible, and preserve the meanings of existing
declarations. A successful Lean build certifies the encoded statement, so review
the statement and its mathematical interpretation as well as its proof.

## Add a module

1. Put completed definitions and proofs in `Quillen/<Subject>/<Topic>.lean`.
   Extend an existing mathematical directory when it fits. A new subject can
   introduce a new directory; there is no fixed list of allowed subjects.
2. Import the smallest modules needed by the implementation. Do not import
   `Quillen`, a generated whole-family entrypoint, tests, audits, or a downstream
   client from implementation code. This keeps the dependency graph reusable
   and prevents cycles.
3. Add a module docstring explaining its objects, main declarations, assumptions,
   and references. Use English, descriptive names, and the applicable
   [mathlib style](https://leanprover-community.github.io/contribute/style.html)
   and [documentation conventions](https://leanprover-community.github.io/contribute/doc.html).
   New file headers should identify authors and Apache-2.0 licensing.
4. Run `python3 scripts/generate_imports.py`. The complete entrypoint discovers
   all library modules. Generated family entrypoints discover their subjects'
   modules; the existing hand-maintained `Library`, `Scheme`, and `Resolution`
   entrypoints retain their public API selection.
5. Add a useful client example or regression probe when it exercises a public
   API, a subtle premise, or a previously broken behavior. Clients belong under
   `examples/downstream/Consumer/`; library code must never depend on them.
   Add its import to `examples/downstream/Consumer.lean`.
6. Run the checks below and update the relevant API/scope documentation when the
   theorem family's meaning or public import changes.

Unfinished proofs and exploratory files stay outside `Quillen/` and the
production import graph. An explicit hypothesis can support a conditional
theorem, but do not disguise a missing theorem as an axiom or assume the desired
conclusion. `sorry`, `admit`, custom axioms, and nonstandard axiom dependencies
are rejected by the release checks.

## Checks

Fast structural checks:

```sh
python3 scripts/generate_imports.py --check
python3 scripts/check_library_layout.py
python3 scripts/check_placeholders.py
python3 -m unittest discover -s scripts -p 'test_*.py'
```

For an individual module during development:

```sh
lake build Quillen.CategoryTheory.ExactCategory.Basic
```

Before integrating a change:

```sh
bash scripts/audit.sh --rehash
```

The final command builds the complete library and public entrypoints, builds
the separately configured downstream package, and replays the kernel axiom
audits even if Lake reused build products. CI runs the same procedure. The
lexical placeholder check is an early diagnostic; the declaration dependency
audit is the trust check.

Historical proofs are not permanently frozen by hashes or a migration ledger.
Edit them normally, explain any changed assumptions or API, and run the relevant
checks. Historical checkpoint claims remain historical; update current scope
documentation from the current source.

## Public APIs and compatibility

Use natural mathematical namespaces. Module paths describe dependency ownership
and need not exactly match declaration namespaces. Prefer small modules and
computation lemmas for the actual maps over duplicate definitions or aliases of
whole developments.

`Quillen.Library`, `Quillen.Scheme`, `Quillen.Resolution`, and the modules listed
in the library guide are preferred client entrypoints. Other canonical modules
are also importable, but their implementation APIs may change more frequently.
Avoid growing `Quillen.Library` for every new helper: the generated complete
root already enrolls all source modules for checking.

While the version is `0.x`, publish breaking import, namespace, hypothesis, or
toolchain changes with a minor-version bump and migration notes. Use a patch
release for compatible corrections. Preserve deprecated declaration aliases or
small compatibility modules for one minor release when practical; record
intentional removals and their replacements. Do not generate a second copy of
the mathematical implementation to preserve compatibility.

Consumers should use a release tag or exact commit, rather than an unpinned
branch. A theorem's premises remain part of its API even when its name stays
the same.

## Dependency upgrades

Ordinary builds use the committed `lean-toolchain`, `lakefile.toml`, and
`lake-manifest.json`. Do not run `lake update` just to check a change.

An intentional upgrade must update the Lean/mathlib pins, both root and
downstream manifests/toolchains, obtain the matching third-party cache, build
the complete library, run the audits, and explain any statement or API changes.
Keep dependency upgrades separate from unrelated mathematical edits when
possible. Cache contents are never committed.

## Releases

Run the complete checks on the exact release commit. Record the toolchain,
dependency revisions, mathematical scope, and actual results in release notes.
Tag that commit, update the package version, and give downstream users a pinned
dependency example. Incomplete theorem families must remain identified as open;
an import path or a green build does not close them.

Contributions are licensed under the repository's Apache-2.0 license.
