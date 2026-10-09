# Actual vertical mapping paths and base restriction

Frozen source boundary: `logs/fiberwise-mapping-path-model-sources.sha256`.
The two modules are `FiberwiseMappingPath/Basic` and `Restriction`.

For `f : E → F` and `q : F → B`, `Space q f` stores an original source point
and a compact-open path starting at its image, all of whose points have the
same displayed base coordinate. Source, endpoint and constant-path inclusion
are literal coordinate maps. Source/target/base universes are independent.

`inclusionHomotopyEquiv q f` is a genuine homotopy equivalence with exactly the
constant-path inclusion forward and exactly source projection inverse. Its
inverse homotopy scales the entire original path by `(1-t)*s`. The scaling
fixes the constant-path image and stays over the original base coordinate.
There are no lifting, separation, weak-equivalence or nonemptiness hypotheses.

For an arbitrary base subset `U`, `restrictionHomeomorph q f U` identifies
the endpoint restriction with the same vertical mapping-path construction on
the actual restricted source and target. It packs or forgets subtype proofs
at every original path value. Endpoint commutation is exact. No openness
assumption is needed for this homeomorphism.

## Validation

Both exact sources compiled warning-free. The author audit scans all 70
actual defining-module origins, including generated helpers, and checks
15 independent-universe consumers for original maps, both genuine inverse
laws, full scaling paths, base coordinates and both restriction round trips.
All recursive axioms are among `propext`, `Classical.choice`, `Quot.sound`.

- Audit: `audits/VerticalMappingPathModelAudit.lean`
- Initial all-origin/consumer log: `logs/fiberwise-mapping-path-model-audit-initial.log`
- Basic check: `logs/fiberwise-mapping-path-basic-check1.log` (process exit 0)
- Restriction final check: `logs/fiberwise-mapping-path-restriction-check2.log`

Later endpoint lifting/locality has a separate source and review boundary.
No global bar-fiber or Waldhausen fibration theorem is asserted here.
