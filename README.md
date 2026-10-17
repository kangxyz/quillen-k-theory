# Quillen K-theory

A Lean library for algebraic K-theory, including Quillen's Q-construction,
Waldhausen's S-construction and scheme K/G-theory, built on Mathlib and
[Aglib](https://github.com/kangxyz/aglib).

## Installation and use

Use the pinned [Lean toolchain](lean-toolchain). Add this to your project's
`lakefile.toml`:

```toml
[[require]]
name = "quillen-k-theory"
git = "https://github.com/kangxyz/quillen-k-theory.git"
rev = "main"
```

Run `lake update quillen-k-theory`, obtain matching dependency artifacts, then
build the required client target and its affected dependencies. Use a specific commit
instead of `main` and retain `lake-manifest.json` for reproducible builds.

Import `Quillen.KTheory.API` for the K-theory interface, or `Quillen` for the
complete library. The [API reference](docs/reference/API.md) lists focused imports.

## Documentation and checks

Start with the [documentation map](docs/README.md).
[Mathematical scope](docs/reference/Scope.md) records hypotheses, coverage and
remaining comparisons; constructed interfaces do not supply their required inputs.

From the library checkout, fetch matching Mathlib artifacts when needed, then
build the required leaf and its affected consumers:

```sh
bash scripts/cache.sh
lake build Quillen.KTheory.API
```

[Contributing](CONTRIBUTING.md#tests-and-checks) explains incremental validation
for development, merge, and publication. `bash scripts/check.sh --rehash` is an
explicit comprehensive diagnostic and CI pipeline, not a normal local acceptance
step. All normal workflows must use incremental checks, including applicable
compilation, lint, affected library/client tests and source/trust checks.
Develop with incremental compilation and its diagnostics; independent lint and
tests run only in the task's final validation before delivery.

## License

[Apache-2.0](LICENSE).
