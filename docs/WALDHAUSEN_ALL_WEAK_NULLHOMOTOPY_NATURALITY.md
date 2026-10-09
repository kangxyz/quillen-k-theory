# The entire original acyclic nullhomotopy

This three-source boundary retains the actual original homotopies, including
all intermediate points and the reversal convention used by the canonical
homotopy-fiber map.

`SConstruction/WeakNaturalTransformationNaturality.lean` proves that the
original categorical nerve cylinder commutes strictly with postcomposition.
It then proves strict precomposition and postcomposition naturality for the
actual weak-natural-transformation simplicial cylinders. The categorical
lemma retains independent source and target object/hom universes; the
S-construction statements use their existing common category-universe pair.

`Topology/Realization/HomotopyNaturality.lean` proves that an actual strict
square of simplicial cylinder maps gives a pointwise equality for the whole
realized homotopies. It uses the existing inverse-cylinder naturality, with
no replacement homotopy or chosen endpoint tracks.

`Fibration/AllWeak/NullhomotopyNaturality.lean` proves the actual original
zero-to-identity cylinder square under the original acyclic inclusion and
change-of-weak map. The source-zero equality is transported by N.zero_eq;
the exact natural-transformation components remain the original zero maps.
Its theorem `AllWeak.contraction_acyclicNullhomotopy` says, for every original
acyclic delooping point x and every interval parameter t, that the all-weak
contraction evaluated on the original change-of-weak image of x, followed by
the original coarse acyclic inclusion, equals `acyclicNullhomotopy N (t,x)`.
The interval reversal is explicit in the proof. Thus it also identifies the
entire path coordinate of `canonicalFiberMap N`.

The final application retains independent category object and hom universes
and needs only coarse two-out-of-three, exactly as required for the actual
all-weak-source acyclic-inclusion exact functor. No extension axiom, cylinder,
projectivity, finite bound, or geometric assumption is added. The generic
realization lemma has its ordinary simplicial-set universe restriction.

No global relative fiber theorem, homotopy-cartesian square, or canonical
homotopy-fiber equivalence is assumed or concluded here. Those remain
separate substantive obligations.

All three focused source checks pass warning-free. The single-pass recursive
origin audit and actual-map, full-path, endpoint, fixed-zero and arbitrary
scheme consumers are in `audits/AllWeakNullhomotopyNaturalityAudit.lean`.
The initial audit passed all7 origins, split [4,1,2], and all9 consumers
warning-free. The fixed7 author guard replay also passed warning-free in
`logs/all-weak-nullhomotopy-naturality-audit-final.log`. Independent review is
accepted: fresh3/fixed7/13 consumers passed with all dependency hashes
unchanged; see `docs/REVIEW_20261009_ALL_WEAK_NULLHOMOTOPY_NATURALITY.md`. Production hashes are frozen in
`logs/all-weak-nullhomotopy-naturality-sources.sha256`.
