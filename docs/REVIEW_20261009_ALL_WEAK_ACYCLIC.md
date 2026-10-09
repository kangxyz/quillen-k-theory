# Independent review: original all-acyclic category and inclusion

Accepted 2026-10-09 12:28:00 UTC.

Both complete frozen sources, `AllWeak/AcyclicEquivalence` and
`AllWeak/AcyclicInclusion`, were read. The manifest is
`logs/all-weak-acyclic-sources.sha256`.

The actual full category of all-weak acyclic objects is equivalent to the
original category by its original inclusion and the lift inserting only
the trivial proposition witness. Both composites are strict identities.
Both directions are genuinely exact for the inherited original fine
structure, including actual pushouts, and preserve the original zeros.
The original weak and cofibration predicates are reflected literally.

For an arbitrary nested pair, every original map between coarse-acyclic
objects is coarse weak by the separately proved two-out-of-three argument.
This proves that the original acyclic inclusion is exact from the all-weak
source to the original coarse structure. The actual simplicial and
realized triangles are proved as equalities. The zero-to-identity
transformation component maps to the original zero-to-acyclic-inclusion
component with precisely the supplied chosen-zero equality. This component
and zero-object equality need no two-out-of-three hypothesis; that input is
retained only where coarse exactness requires it.

Independent object/hom universes are preserved. These categorical results
do not silently identify the double-S base; the later ordinary-row
natural isomorphism is a separate proof. No global fibration, continuous
inverse family, or canonical nullhomotopy compatibility is assumed.

Fresh excluded-target2 rebuilding passed the fixed recursive origin count
**22 = 17 + 5**, allowing only standard Lean axioms, and all **25 consumers**.
The author's19 are retained; six additions check both original inverse
morphism formulas, the unchanged fine predicate, the zero-transformation
and zero-object formulas without saturation, and the evaluated original
realized triangle. The first independent run was warning-free with no
consumer/source repair. All target hashes, **3,492 prerequisite-source**,
**16,064 artifact**, and project/toolchain hashes match before/after.

Evidence:
- Audit: `audits/AllWeakAcyclicIndependentAudit.lean`
- Preparation: `logs/prepare-all-weak-acyclic-independent.py`
- Replay: `logs/verify-all-weak-acyclic-independent.sh`
- Driver: `logs/all-weak-acyclic-independent-driver.log`
- Manifest: `logs/all-weak-acyclic-independent-20261009/artifacts.sha256`

This accepted endpoint is outside the frozen12:10 archive.
