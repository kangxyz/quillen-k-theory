# Independent review: original collar strict-fiber HELP transport

Accepted 2026-10-09 12:40:05 UTC.

## Frozen source

`Quillen/CategoryTheory/TheoremB/CompactCollarFibers.lean`.
Manifest: `logs/compact-collar-fibers-sources.sha256`.
The complete source and its actual-map prerequisites were read; no production
source or live artifact is edited. This is after the 12:10 archive freeze.

## Semantic assessment

The generic theorem concerns an actual total-space homotopy equivalence
`e:E≃F` and a genuine HLP projection `q:F→B`. Its explicit additional
hypothesis is full compact HELP of the original strict-fiber map induced by
`e` over `q`, at the chosen base point. This premise is retained; the theorem
does not derive it from the total homotopy equivalence.

The proof transports along the actual canonical homotopy-fiber source map,
whose homotopy equivalence is already proved for an arbitrary total homotopy
equivalence. Genuine HLP of `q` supplies the homotopy equivalence from its
strict fiber to its homotopy fiber, with the original constant-path inclusion
as forward map. These two facts and the assumed HELP of the actual comparison
fiber give HELP of the exact composite. The point/path triangle commutes
literally: the source map changes the point by `e` and retains the constant
path. Cancelling the canonical homotopy-fiber source map proves HELP for the
original strict-fiber inclusion of `q ∘ e`. No inverse over the base and no
HLP of `q ∘ e` is required or inferred.

The left and right collar wrappers use the actual collar comparison into
the genuine endpoint pullback, and the established total-space comparison
homotopy equivalence with that exact forward map. Their target projection
has genuine HLP by base change of the corresponding endpoint map. The strict
comparison fibers are explicitly defined using the original collar map,
endpoint pullback projection and original collar comparison. The wrappers
retain the premise that this specific strict-fiber comparison has compact
HELP. The conclusion is full HELP of the original collar strict-fiber
inclusion, including its original point and entire constant path.

The left cutoff requires `0 < cut`; the right cutoff requires `cut < 1`.
Only the corresponding endpoint HLP and specific comparison-fiber HELP
premises are used. Neither wrapper assumes or proves HLP of the original
collar. Source/target/base spaces retain the established common-universe
contract of HLP and compact HELP. No nonemptiness or separation assumptions
are added.

## Independent verification

A fresh first-path overlay excludes the target artifact family and rebuilds
the exact frozen source. One declaration traversal recursively verifies all
**7** target origins, with a fixed guard and only `propext`, `Classical.choice`
and `Quot.sound` accepted.

The **12 consumers** retain the two authored generic/full-boundary tests and
add actual left/right theorem applications in place of signature-only
checks, exact original comparison point pairs on both strict fibers,
constant-path values for both original collar inclusions, the generic
source-map triangle, original point/path coordinates and actual canonical
source-equivalence forward map.

Audit: `audits/CompactCollarFibersIndependentAudit.lean`.
Replay: `logs/verify-compact-collar-fibers-independent.sh`.
Evidence directory: `logs/compact-collar-fibers-independent-20261009/`.

## Remaining scope

The actual comparison-fiber HELP inputs must still be proved, for example
by the separately owned height-case analysis. This source is a correct
transport adapter, not a proof that those inputs already hold. Variable-base
collar lifting, global gluing and the final Waldhausen fibration theorem
remain separate obligations.

## Terminal evidence

The fresh source rebuild and fixed7/all12 consumer audit passed warning-free.
No implementation or consumer repair was required. The source hash,
**3,406 prerequisite-source hashes**, **15,750 dependency-artifact hashes**
and project/toolchain pins match before and after. The target olean is a
fresh regular file, and actual first-path import resolution is recorded.

- Terminal driver: `logs/compact-collar-fibers-independent-driver.log`
- Source/import log: `logs/compact-collar-fibers-independent-20261009/check.log`
- Audit log: `logs/compact-collar-fibers-independent-20261009/audit.log`
- Evidence manifest: `logs/compact-collar-fibers-independent-20261009/artifacts.sha256`
