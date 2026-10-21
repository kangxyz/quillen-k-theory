# Shared source maintenance

Quillen keeps its mathematical sources and declarative CI data. Standard source
maintenance lives in the common `lean_ci` distribution:

```sh
python3 -m lean_ci imports --config .github/lean-ci.toml --root . --check
python3 -m lean_ci imports --config .github/lean-ci.toml --root . --write
```

The shared authoring command preserves manual ownership, source credits, import
wrapping and declared facade roles. It validates all prospective imports and
cycles before guarded atomic writes. The historical marker spelling remains
unchanged so source relocation does not transfer ownership or rewrite mathematics.

[CONTRIBUTING](../CONTRIBUTING.md#tests-and-checks) owns normal focused proof
iteration and common final checks. Shared tooling contract fixtures live with
the common package; this directory contains no independent CI implementation.
