# Lean performance findings

Use the shared Aglib methods and this library's
[local cases](performance/local-cases.md). Current commands and finite-budget
policy belong to [CONTRIBUTING](../CONTRIBUTING.md#tests-and-checks)
and [development](DEVELOPMENT.md#affected-check-scope). Preserve the
[standard-budget and finite-local-allowance policy](../CONTRIBUTING.md#typechecking-performance).

| Problem | Read |
| --- | --- |
| Concrete equality, homotopy, dependent-node or structure-field conversion | [Shared conversion methods](https://github.com/kangxyz/aglib/blob/main/docs/performance/conversion-boundaries.md), [local examples](performance/local-cases.md#evaluation-and-node-transports) |
| Repeated instances or a generic theorem that becomes expensive on application | [Instances](https://github.com/kangxyz/aglib/blob/main/docs/performance/instances-and-universes.md), [shared constructions](https://github.com/kangxyz/aglib/blob/main/docs/performance/shared-constructions.md), [vector-bundle case](performance/local-cases.md#vector-bundle-instance-inference) |
| No accepted default-budget repair | [Recorded finite allowances](performance/local-cases.md#retained-finite-allowances) |
| Rebuild, input metadata or checker setup | [Common build/check lessons](https://github.com/kangxyz/aglib/blob/main/docs/performance/build-and-check-costs.md), [older-pin workaround](performance/local-cases.md#historical-hardlink-workaround) |
| Explicitly requested timing or cause investigation | [Diagnosis and evidence](https://github.com/kangxyz/aglib/blob/main/docs/performance/diagnosis-and-evidence.md) |

Keep the original mathematical interfaces and actual source/dependency basis.
A passing module establishes its recorded scope; it does not automatically
establish a speedup, consumer success or a compiler cause.

## Repair workflow

For serious compilation trouble, use the lookup and read the matching case
before further experiments or budget changes. When its conditions do not
cover the failure, use the shared
[upstream reference search](https://github.com/kangxyz/aglib/blob/main/docs/performance/diagnosis-and-evidence.md#search-upstream-references)
and check the pinned implementation. Ordinary repair uses incremental
compilation and compatible retained evidence; profiling is an explicitly
requested diagnostic.

When a validated repair adds new reusable knowledge, update the relevant
`docs/performance/` topic. Merge repeated experience; keep its symptom and
conditions, effective change, important failed alternative or limit, and
existing evidence. Another run or pass of a known method needs no entry.
Common methods have one Aglib owner; retain Quillen-specific cases here and
keep this entry page short. Documentation creates no new benchmark or
acceptance cycle.
