# Independent review: canonical fiber factorization and common-base square

Accepted 2026-10-09 13:45:39 UTC.

Both complete sources in `logs/all-weak-fiber-square-sources.sha256` were
read: `Waldhausen/Fibration/AllWeak/CanonicalFiberFactorization` and
`Topology/HomotopyFiber/CommonBaseSquare`, under `Quillen`.

## Canonical factorization

The actual all-weak contraction is evaluated after the original
change-of-weak map to give a literal homotopy-fiber lift. Its source
coordinate is unchanged, the full stored path is that exact contraction,
and projection after the lift is strictly identity. The separately proved
contracted-base projection homotopy equivalence, followed by genuine
homotopy-equivalence cancellation, proves this exact lift is an HE. Its
inverse is the original projection. The fixed-zero contraction proves
preservation of the original constant-path basepoint, and every finite
based homotopy degree includes zero.

The original acyclic-inclusion square gives the actual map between the
original change-of-weak homotopy fibers. It applies the fine inclusion to
the source and the coarse inclusion to the entire path. Both path endpoint
conditions use the proved original square and exact chosen-zero equality.
The recently accepted whole-nullhomotopy identity proves the composite
with the contraction lift equals the original canonicalFiberMap strictly,
including its stored path. Independent object/hom universes remain valid.
Only the actual coarse two-out-of-three hypothesis is used here.

No equivalence of the second factor is assumed or concluded. The global
relative-fiber theorem and the resulting homotopy-cartesian transport are
still distinct obligations.

## Common-base square

For actual maps p, q and j with q composed with j equal to p, the original
homotopy fiber of p is homeomorphic to the literal strict pullback of the
original homotopy-fiber projection of q. Both directions retain the actual
source coordinate and entire original path. The inverse endpoint condition
is derived from the displayed strict pullback equality.

The original homotopy-fiber projection already has genuine HLP for arbitrary
q. Its strict-pullback comparison is therefore a genuine HE. Composing with
the literal homeomorphism proves the original common-base comparison is an
HE. The inner path is unchanged and the outer comparison path is exactly
constant. No HLP of p or q, separation, nonemptiness, or global realization
fiber theorem is required. The existing common-universe topology scope is
explicit. The actual original relative-inclusion consumer uses precisely
these maps without claiming its missing global fiber identification.

## Independent verification

The separate first-path overlay excludes both target artifact families and
rebuilds the frozen sources in order. The fixed-origin recursive audit
checks **41 = 20 + 21** declarations. Its **37 consumers** include the
31 authored original-coordinate, full-path, basepoint, all finite degrees,
zero-degree, arbitrary-scheme and original-relative-map cases. Six further
checks retain both actual homeomorphism inverse laws, the lift's actual
right inverse homotopy, original-map weakness of both HEs, and the outer
path's pointwise constant formula.

- Audit: `audits/AllWeakFiberSquareIndependentAudit.lean`
- Preparation: `logs/prepare-all-weak-fiber-square-independent.py`
- Replay: `logs/verify-all-weak-fiber-square-independent.sh`
- Final replay: `logs/verify-all-weak-fiber-square-independent-final.sh`
- Evidence directory: `logs/all-weak-fiber-square-independent-20261009`

The fresh two-source build and final fixed 41 / 37-consumer replay passed
warning-free. The initial extra weakness consumers lacked the separate
WeakEquivalenceProperty import; adding it repaired only the review audit.
No production source changed. All initial target/dependency hashes were
rechecked before expanding the manifest to the full audit import closure,
including all consumer and metaprogram imports. The final **4,736 source**,
**22,223 artifact** and project/toolchain-pin hashes agree before and after.
Initial narrower dependency manifests and initial diagnostics are retained.
These sources are outside the frozen 12:10 archive.
