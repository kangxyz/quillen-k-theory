# Missing weak-cartesian finite cube: exact scope

The required theorem concerns a strictly commuting map between two actual
pushout squares. Their corresponding attaching legs are cofibrations. It must
derive weak cartesianness of the two outgoing faces from weak cartesianness of
the two incoming faces, retaining the original constant-path comparisons into
the actual compact-open-path homotopy pullbacks.

A sufficient first scope allows all eight original spaces and maps to be actual
simplicial realizations, both squares to be realized simplicial pushouts, and
the attaching legs to be realized monomorphisms. The existing
`CartesianPushout.exists_leftHomotopyEquiv` and its right counterpart prove the
stronger-map-input theorem, using genuine incoming homotopy equivalences.
They do not prove this weak-input theorem.

## Empty spaces must be covered

“All finite based homotopy maps are bijective at every source point” alone is
vacuous for an empty source. A complete weak property must additionally control
target components, for example by requiring every target point to be joined to
an image point. An equivalent nonempty-target/nonempty-source condition can
supplement the all-degree test. For nonempty row spaces the actual chosen zero
provides a source point. Empty degree-zero boundaries require a separate proof
that the corresponding pullback target is empty.

## The precise unavailable step

The existing chain `DoubleCylinderCartesian` → `FiniteNormalization` →
`NormalizedFibrationSpan` constructs global fiberwise strong-deformation data
on whole path-space pullbacks. Those parameter spaces need not be compact.
Actual compact HELP therefore cannot simply be substituted for the supplied
homotopy equivalences. Selecting one inverse at each point is not a continuous
family. The accepted product comparison has exact compact-source lifts and
compact HELP, not an unrestricted ordinary-product homeomorphism.

The accepted `homotopyEquivOfCompactHELP` theorem applies when both its spaces
are actual simplicial realizations. Its use on a homotopy-pullback target would
require a separately proved suitable realization/CW-type model and the correct
original-map identification. Such a model is not currently supplied.

A direct route needs a genuine compact-parametric local-gluing or weak cube
proof. Another route needs additional weak disk-lifting/Whitehead and
homotopy-pullback CW-type infrastructure; neither may be assumed.

The connected-row diagonal fiber theorem is a special case of
[Bousfield–Friedlander, Theorem B.4, pp.121–124](https://ncatlab.org/nlab/files/BousfieldFriedlanderSpectra.pdf).
Their proof passes through the bisimplicial model structure and a diagonal Kan
fibration criterion. These are not existing imported theorems in this library,
so the reference locates the mathematical obligation rather than discharging it.

This document records an open proof boundary. It is not a conditional replacement
for the requested fibration theorem and adds no assumption to accepted endpoints.

## Additional accepted input (2026-10-09 10:15–10:22 UTC)

Full compact HELP on all original fibers of a genuine fibration square now
implies literal RLP of the original total comparison's mapping-path endpoint
against every realized simplicial monomorphism. The proof extends actual
simplex tests through the relative skeleton. Thus relative-cell constructions
can use this RLP on arbitrary realized test pairs, including noncompact ones.
This does not provide lifting on arbitrary non-realization parameter spaces
or a global continuous inverse on a path-space pullback. See
[the independent review](REVIEW_20261009_FIBERWISE_REALIZATION_LIFTING.md).

The original drop and evaluation bar augmentations now also induce genuine
homotopy equivalences of their actual path-space fibers, by a separately
proved genuine square-fiber theorem. Consequently transport from a bar or
replacement global fiber to the original diagonal fiber is available with
actual maps. The identification of a single row fiber with that global
replacement fiber is still the remaining obligation. See
[the independent review](REVIEW_20261009_SQUARE_BAR_FIBER_HOMOTOPY.md).
