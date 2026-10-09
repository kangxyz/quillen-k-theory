# Initial standalone release: v0.1.0

This release publishes the 2026-10-09 checkpoint as an independently reusable
Lake library under Apache-2.0. The mathematical development remains incomplete;
see [STATUS.md](STATUS.md).

## Changes

- Preserve all existing mathematical modules and declaration names.
- Generate the complete `Quillen` import surface and optional subject facades.
- Keep selected public entrypoints and independently configured client examples.
- Check dynamically discovered sources, import cycles, production/client
  separation, and generated-entry consistency without freezing future proofs.
- Add CI, contribution and architecture guides, package metadata, and licensing.
- Separate current scope and release verification from historical checkpoint
  reports; omit caches, raw run logs, and checkpoint-only machinery.

## Reproduction

```sh
bash scripts/cache.sh
python3 -m unittest discover -s scripts -p 'test_*.py'
bash scripts/audit.sh --rehash
```

Exact runtime: Lean 4.34.0. Exact mathlib revision:
`5ed2965256430c3649e86755f9576b54eca72435`. The committed manifests lock all
transitive dependencies. Library checks use no previous project build cache;
only third-party dependency caches may be reused.

## Verification results

The standalone release verification is in progress. Results will be recorded
here before the publication tag is created.
