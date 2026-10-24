# Lean performance findings

This guide keeps the reusable local methods and repair process. Complete
[case records](performance/README.md) retain the original conditions,
measurements, failed approaches and source/evidence identities.
Use [Aglib's method synthesis](https://github.com/kangxyz/aglib/blob/main/docs/PERFORMANCE.md)
for the common conversion, constructor, instance and build-cost techniques.

## Key methods and conditions

**Reuse actual proof instances and finite witnesses.** When over-site inference
repeats sheafification/local-bijectivity search or reconstructs an unchanged
finite generator index, bind the existing universal proof instances locally and
pass the existing finite-index witness directly. Keep the original cover,
basis and transport construction. The vector-bundle record has a matched
module comparison; its timings do not establish a whole-library speedup.
[Full case](performance/vector-bundle-instance-inference.md).

**Share a statement under the checker's actual transparency.** A declaration
can compile while the pinned linter's `checkType` finds its concrete type too
expensive. The seed-factorization repair used the same transparent generic
properties over the actual Laurent track, functor and natural seed; local
irreducibility did not shield types from full transparency.
[Full case](performance/stable-seed-factorization-types.md).

**Transport complete data before projecting.** Compare whole relative homotopies
before taking level maps. For outer isomorphism congruence, type the existing
comparison itself; naming inner equalities alone can move the failure outward.
For dependent-node families, keep the original Model arrows, finite index and
literal transport equations together before concrete evaluation.
[Evaluation-unit cases](performance/evaluation-unit-comparison-proofs.md),
[full-node overlap](performance/full-node-overlap-reanchoring.md).

**Keep necessary finite allowances honest.** A tested allowance is a resource
condition, not an optimization or a proved minimum. The recorded 800,000 pass,
smallest tested 550,000 pass and nonminimal 400,000 pass have distinct evidence.
Keep the standard package default and documented declaration-local exceptions
under [the existing policy](../CONTRIBUTING.md#typechecking-performance).
Choosing an allowance does not require profiling.
[Original cases](performance/mixed-cylinder-naturality.md).

**Distinguish observer failures from checker findings.** Resolve the actual
artifact/source basis and retain compatible successes. The old-pin private
reflink preparation is a historical workaround; the current toolkit rechecks
native content for ctime-only link metadata changes.
[Complete older-pin case](performance/shared-cache-metadata-during-final-checks.md).

## Repair workflow

1. Identify the phase from existing feedback and use the relevant method and
   case, checking its compiler, source, structures, universes and budget basis.
   At a bottleneck, actively use targeted compiler diagnostics, scoped traces,
   profiling or scratch probes when feedback cannot guide the next repair.
   Normal troubleshooting and targeted diagnosis need no separate user approval.
2. Preserve original seeds, clocks, maps, hypotheses and the needed reduction
   interface; make a bounded repair at the actual comparison/search boundary.
3. Compile the affected module incrementally and include actual in-package
   consumers when implicated. Retain compatible artifacts and passed check
   categories instead of restarting the library.
4. If no known case applies, use Aglib's
   [upstream reference-search method](https://github.com/kangxyz/aglib/blob/main/docs/PERFORMANCE.md#search-upstream-references).
5. When a validated repair adds new reusable knowledge, save or update its
   complete case under `docs/performance/` and refine the applicable method here.

Current commands and check scope remain in
[CONTRIBUTING](../CONTRIBUTING.md#tests-and-checks)
and [development](DEVELOPMENT.md#affected-check-scope).
Historical client, control and replay stages in case records are not current
requirements. A leaf pass retains its own scope; unmatched/profiled observations
cannot be turned into a controlled speedup, enclosing-graph pass or compiler cause.

## Preserve both layers

Keep the actionable methods/process here and every complete case in
[the folder](performance/README.md), including original failures and evidence
limits. Neither a summary nor an index replaces the case text; preserving case
text also does not remove the method synthesis from this guide. Recording
experience adds no benchmark, build or acceptance cycle. Another run/pass or
unchanged application needs no new entry; this does not permit deleting or
shortening any existing case.
