# Original weak equivalences and finite cube-boundary HELP

**Author checked and frozen, 2026-10-09 14:02:24 UTC.** All four sources
compile warning-free. The terminal single-pass recursive origin audit checked
**87 = 4 + 66 + 2 + 15** declarations and **24 actual-map consumers**.
Independent fresh review is assigned and remains pending.

## New source boundary

1. `Quillen/Topology/HELP/WeakFiniteBased.lean`
2. `Quillen/Topology/HELP/CubicalHorn.lean`
3. `Quillen/Topology/HELP/WeakCubeFilling.lean`
4. `Quillen/Topology/HELP/WeakFinite.lean`

No earlier accepted sources or public definitions are changed. All four files
are beyond the immutable 12:10 archive boundary.

## Actual geometric route

The constant-boundary layer uses the original cubical homotopy-set surjection,
then genuine HEP and exact boundary-path correction. It separately retains
the empty-boundary zero-dimensional test. This layer alone does not lift
arbitrary positive-dimensional boundary maps.

The substantive reduction defines the horn as the literal subset of
`I^n × I` consisting of side faces or height zero. Lowering the height stays
in that horn; after reaching height zero, coordinate contraction of the bottom
cube contracts the whole horn. The horn and top cube cover the entire product
boundary. Their literal sum map is a continuous surjection from a compact
space to a Hausdorff space, hence an actual quotient. Agreement on the original
top rim gives a genuine displayed pushout. The horn inclusion consequently
has HEP by cobase change of the proved cube-boundary inclusion HEP. The whole
product boundary identifies with the next actual cube boundary by the original
first-coordinate homeomorphism.

For a space with singleton based finite homotopy sets, an arbitrary boundary
map is normalized on the horn using that HEP and the explicit contraction.
Its top face then becomes an actual generalized loop. Equality with the
constant loop in the genuine homotopy quotient supplies a homotopy relative
to the whole top rim. Reversing its time coordinate fills the product cube.
Whole-boundary HEP restores the exact original boundary map. Dimension zero
uses explicit nonemptiness; it is not obtained from vacuous pointed tests.

For an original weak map `f`, form its actual homotopy pullback along the given
cube map `b`. Its original base projection is weak by the accepted actual-fiber
proof. Since the cube is contractible, injectivity of that projection on each
finite homotopy set gives singleton homotopy sets of the pullback. Component
surjectivity supplies an actual point. The arbitrary boundary map into this
pullback includes the entire originally prescribed path, and the geometric
filling extends it literally.

The extended map's parameter coordinate need not initially equal the cube
identity. Explicit straight interpolation corrects it through the genuine HLP
of the actual homotopy-pullback projection. The proved duration vanishes exactly
on the original cube boundary, so stationary lifting fixes every boundary
pullback point. In particular its complete stored path, not just its two
endpoints, remains unchanged. Projecting the final section to the source and
its path coordinates gives exactly the requested full finite HELP.

## Checked endpoints

- `IsWeakHomotopyEquivalence.cube_fullHELP`: for every finite dimension, arbitrary
  original boundary map and arbitrary prescribed boundary homotopy, a cube
  extension with the entire original boundary path fixed at every time.
- `IsWeakHomotopyEquivalence.cube_strictHELP`: original strict-square specialization,
  with a homotopy relative to the complete original boundary.
- `IsWeakHomotopyEquivalence.mappingPath_endpoint_boundaryLifting`: the original
  ordinary mapping-path endpoint satisfies `CubicalSubdivision.BoundaryLifting`
  on literal unlifted finite cubes, including dimension zero.

The ambient spaces have a common arbitrary universe, as required by the
accepted HLP APIs. The endpoint test coordinates are the unchanged finite cubes.
No continuous inverse or global contraction of the original weak map is chosen.
There is no upgrade to homotopy equivalence or to HELP on arbitrary compact
pairs. Adapting later collar/finite recursion from its older full-compact input
to this exact finite contract is a separate obligation.

## Validation

Author audit: `audits/WeakFiniteHELPAudit.lean`. The single traversal checks every
defining-module origin recursively, including generated/private helpers, with
only `propext`, `Classical.choice` and `Quot.sound` permitted. It tests the literal
horn coordinates, quotient/pushout and HEP, boundary coordinate homeomorphism,
arbitrary sphere filling, straight interpolation, original full prescribed
paths, actual endpoint map and explicit dimension-zero cases. The fixed87 guard is now installed for independent replay.

Frozen ordered manifest: `logs/weak-finite-help-sources.sha256`
(fingerprint `5f1d0a16fe3713a0ae90777453ab7f54694e92e164cc2ab8db72c94cf2f93d14`).
Terminal author log: `logs/weak-finite-help-audit-initial.log`.
Final source/audit replay: `logs/verify-weak-finite-help.sh`.

The focused development checks required only elaboration repairs: explicit
section hypotheses, record layout, finite closed-union notation, original
map coercions and the actual pushout cocone, plus a typed proof-local instance.
The final source was restyled from `letI` to typed `let` to remove its sole
style warning. The arbitrary-boundary filling and all exact-map consumers
pass with no sorry or nonstandard axioms. Earlier diagnostic logs are retained.
