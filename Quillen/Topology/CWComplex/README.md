# Classical CW geometry and covers

## Public imports

Module paths are relative to `Quillen.` unless fully qualified.

| Import | Interface |
| --- | --- |
| [`Quillen.Topology.CWComplex.SimplyConnectedCover`](SimplyConnectedCover.lean) | Constructed same-universe simply connected surjective cover of an actual connected Hausdorff CW subtype; `Quillen.ClassicalCW.exists_simplyConnected_cover` |
| [`Quillen.Topology.CWComplex.UniverseTransport`](UniverseTransport.lean) | Actual intrinsic CW subtype and literal ULift geometry |
| [`Topology.CWComplex.Whitehead`](Whitehead.lean) | `Quillen.ClassicalCW.homotopyEquivOfWeakHomotopyEquivalence` with the exact original forward map |
| [`Topology.CWComplex.Subtype`](Subtype.lean), [`Topology.CWComplex.ULift`](ULift.lean), [`Topology.CWComplex.UniverseTransport`](UniverseTransport.lean) | `Quillen.ClassicalCW.subtypeCWComplex`, `uliftCWComplex`, `uliftSubtypeCWComplex` and original-chart equations |

## Constructed simply connected covers

[`ClassicalCW.exists_simplyConnected_cover`](SimplyConnectedCover.lean)
starts with an actual CW subtype `C` in a Hausdorff `X : Type u` and
`ConnectedSpace C`. It produces `E : Type u`, its topology and a continuous
projection `p : E → C` with `IsCoveringMap p`, surjectivity and
`SimplyConnectedSpace E`. Local path connectedness and ambient-thin
neighborhoods are constructed from the original cells and topology;
connectedness then gives path connectedness. The theorem has no supplied
local connector or universal cover.

More generally, `PathThinNeighborhoods.total_simplyConnectedSpace` works for
a path-connected, locally path-connected base with the displayed ambient-thin
neighborhoods. `path_class_endpoint` proves the exact endpoint equation;
`pathLift_endpoint` identifies the literal lifted endpoint with chronological
composition of the initial based class and original path class. The actual
chart-topologized total is path connected, and covering injectivity yields
uniqueness of its path classes.

The lower-level chosen-cover branch keeps its own hypotheses.
`exists_classicalCWComparisonChosenCovers` takes the original double-cylinder
pushout, actual simply connected covers of both ends and the cylinder,
cylinder-cover surjectivity and selected end-cover points. Its commuting lifts
are constructed. The chosen-cover ordinary-uniqueness interface likewise
retains its self-cylinder and cover data. Supplied-cover twisted Whitehead
still takes its explicit commuting lift. Automatic construction in the theorem
above does not erase assumptions from these separate interfaces.

## Actual CW geometry and automatic plus uniqueness

The included classical-CW owners construct characteristic quotients, skeletal
and global lifting, homotopy lifting and Whitehead recognition directly from
actual Hausdorff CW subtypes. No finite-dimensional, countable or locally
finite condition is added. The actual weak map is retained as the forward map
of `ClassicalCW.homotopyEquivOfWeakHomotopyEquivalence`.

`ClassicalCW.locallyPathConnectedSpace` and `pathThinNeighborhoods` construct
the local geometric inputs from the original CW cells and topology.
`ClassicalCW.exists_simplyConnected_cover` then constructs a same-universe
surjective covering with simply connected total space for an actual connected
Hausdorff CW subtype. It does not assume a supplied universal cover.

The actual canonical double cylinder has constructed connectivity, local path
connectedness and thin neighborhoods. Its path-class cover and those of both
ends supply `IsPlusConstruction.classicalCWPlusUnique`, whose only geometric
inputs are the original actual Hausdorff CW subtypes and original same-universe
plus certificates. Ordinary uniqueness follows by self-cylinder homotopy
cancellation. See the [classical CW plus guide](../PlusConstruction/ClassicalCW.md) for the exact maps,
points, tracks, subgroup, and distinction from prescribed-track coherence.

The lower-level chosen-cover branch remains available with explicit actual
covers, cover points, target-cover surjectivity and pushout data; it constructs
the commuting lifts. The separate cover-transfer owners prove actual pullback
covering and simple-connectedness results under a supplied homotopy equivalence
to a local-connector space. Their categorical-realization specialization uses
the constructed resolution and weak/metric equivalences; it does not identify
an arbitrary CW-homotopy-type model with a nerve.
