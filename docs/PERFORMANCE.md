# Lean performance findings

Keep key guidance here and full records in the [case folder](performance/README.md).
The folder preserves every earlier section, its measurements, failed approaches,
source identities and [original conditions](performance/original-context.md).

| Problem | Original records |
| --- | --- |
| Repeated instance inference | [Vector-bundle case](performance/vector-bundle-instance-inference.md) |
| Expensive concrete types or homotopy/evaluation comparisons | [Seed-factorization types](performance/stable-seed-factorization-types.md), [evaluation-unit cases](performance/evaluation-unit-comparison-proofs.md) |
| Dependent-node transport | [Full-node overlap](performance/full-node-overlap-reanchoring.md) |
| Necessary finite local allowance | [Mixed-cylinder cases](performance/mixed-cylinder-naturality.md) |
| Shared cache metadata | [Historical old-pin workaround](performance/shared-cache-metadata-during-final-checks.md) |

Keep original maps, clocks, universes and hypotheses. A passing case retains
its actual scope; a finite allowance is not itself a performance improvement.
Common key guidance is in [Aglib](https://github.com/kangxyz/aglib/blob/main/docs/PERFORMANCE.md).

## Repair workflow

For serious compilation trouble, read the relevant case before further experiments
or budget changes. Check the source/pin conditions and the dependency's cases when
needed. Current commands and finite-budget policy remain in
[CONTRIBUTING](../CONTRIBUTING.md#typechecking-performance)
and [development](DEVELOPMENT.md#affected-check-scope), not historical stage lists.

When no case applies, use upstream reference search by diagnostic, symbol, phase
and version, then check the pinned implementation. Profiling and timing comparisons
remain explicitly requested investigations; ordinary repair is incremental.

## Preserve cases

Save a reusable repair as a case file under `docs/performance/`, retaining its
conditions, failed attempts, effective change and existing evidence. Update the
same case for follow-ups and its folder-index link. Keep the original case details
when refining key guidance; a summary or Git link is not their replacement.
Recording experience adds no new benchmark, build or acceptance cycle.
