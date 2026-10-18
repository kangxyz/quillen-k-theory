# Plus constructions on actual classical CW spaces

## Public imports

Module paths are relative to `Quillen.` unless fully qualified.

| Import | Interface |
| --- | --- |
| [`Topology.PlusConstruction.ClassicalCWUniqueness`](ClassicalCWUniqueness.lean) | Same-universe automatic existence, ordinary cancellation and `IsPlusConstruction.classicalCWPlusUnique` |
| [`Topology.PlusConstruction.ClassicalCWUniquenessUniverseLift`](ClassicalCWUniquenessUniverseLift.lean) | Original-space `classicalCWPlusUnique_commonUniverse`, `classicalCWPlusUnique_successor` and mixed-universe cancellation |
| [`Topology.PlusConstruction.UnivSubtype`](UnivSubtype.lean) | Exact original plus-certificate transport through the canonical whole-space subtype |
| [`Topology.PlusConstruction.ClassicalCWComparison`](ClassicalCWComparison.lean) | Comparison existence with chosen covers and constructed lifts |
| [`Topology.PlusConstruction.ClassicalCWComparisonUniqueness`](ClassicalCWComparisonUniqueness.lean) | Ordinary cancellation/uniqueness with chosen covers |
| [`Topology.CWComplex.SimplyConnectedCover`](../CWComplex/SimplyConnectedCover.lean) | `ClassicalCW.exists_simplyConnected_cover` |
| [`Topology.Covering.PathClassEndpoint`](../Covering/PathClassEndpoint.lean), [`Topology.Covering.PathClassSimplyConnected`](../Covering/PathClassSimplyConnected.lean) | Literal lifted endpoint equation and simply connected path-class total |
| [`Topology.CWComplex.Whitehead`](../CWComplex/Whitehead.lean) | Exact-forward homotopy equivalence for weak equivalences between actual Hausdorff CW subtypes |
| [`Topology.LocalCoefficients.CommonUniverseChains`](../LocalCoefficients/CommonUniverseChains.lean), [`Topology.PlusConstruction.CommonUniverse`](CommonUniverse.lean) | Original chain/certificate transport to an explicit common universe |
| [`Topology.CWComplex.Subtype`](../CWComplex/Subtype.lean), [`Topology.CWComplex.ULift`](../CWComplex/ULift.lean), [`Topology.CWComplex.UniverseTransport`](../CWComplex/UniverseTransport.lean) | Actual intrinsic subtype and literal ULift CW geometry |

## Overview

For two original plus maps between actual Hausdorff classical CW subtypes,
the library constructs a comparison homotopy equivalence under the source and
proves ordinary homotopy uniqueness. Same-universe and mixed-universe theorems
retain the original spaces, maps, points, tracks and subgroup. General mixed
spaces require the displayed common coefficient universe.

The proofs construct the required covers, commuting lifts and canonical double
cylinders from the original data. No finite-dimensional, countable or locally
finite restriction is imposed. Actual CW structures are required; the result
does not transport a bare assertion of CW homotopy type or assert coherence
relative to prescribed tracks. See [verification](../../../docs/reference/Scope.md#verification)
for the current integrated checking scope.

## Exact same-universe automatic theorem

[`Quillen.IsPlusConstruction.classicalCWPlusUnique`](ClassicalCWUniqueness.lean)
has the following original inputs:

- Hausdorff ambient spaces `X₀`, `X₁`, `X₂ : Type u`, subsets `A`, `B`, `C`,
  and actual `CWComplex A`, `CWComplex B`, `CWComplex C` instances

- Continuous maps `f : TopCat.of A ⟶ TopCat.of B` and
  `g : TopCat.of A ⟶ TopCat.of C`

- Points `a : A`, `b : B`, `c : C`, and original tracks
  `γ : Path (f a) b`, `δ : Path (g a) c`

- One subgroup `N : Subgroup (HomotopyGroup.Pi 1 A a)` and the two original
  certificates `IsPlusConstruction.{u,u,u} f.hom γ N` and
  `IsPlusConstruction.{u,u,u} g.hom δ N`

It produces a continuous homotopy equivalence `h : B ≃ₕ C`, proves
`h.toFun.comp f.hom` homotopic to `g.hom`, and proves every continuous
`k : B → C` with `k.comp f.hom` homotopic to `g.hom` ordinarily homotopic to
`h.toFun`. `exists_classicalCWComparison` exposes the existence part.

The certificates themselves provide source/target path connectedness,
perfectness of `N`, based fundamental-group surjectivity with kernel exactly
`N`, and quasi-isomorphisms of the original chain maps for every target local
system in universe `u`. Normality follows from the kernel equality. The maps,
points, tracks and subgroup are not replaced by unrelated choices.

There is no supplied cover, cover point, commuting lift, double cylinder,
pushout proof, domination or desired-homotopy-equivalence certificate in this
automatic statement. Actual CW structure is required: a bare assertion that
a space has CW homotopy type is not this interface.

## What is constructed

The proof uses the literal canonical `TopCat` pushout of the interval-endpoint
map and `endMap f g`. Connectivity follows from the original cylinder, the
source point and target path connectedness. Actual CW characteristic quotients
provide local path connectedness of the ends; the pushout topology supplies it
for the cylinder. Constructed CW thin neighborhoods and the overlapping
two-collar argument give the cylinder thin neighborhoods. No CW or Hausdorff
instance on the cylinder is assumed.

The covers are the literal based-path-class total spaces with their genuine
prebundle chart topology. Their basepoints are the neutral based classes.
The endpoint/universality construction proves covering, surjectivity and
simple connectedness. The chosen-cover comparison then constructs commuting
lifts, proves weak equivalence of the original cylinder legs from their
fundamental-group and twisted-chain results, and recognizes actual homotopy
equivalences using classical-CW lifting. The original full cylinder and the
right-leg inverse law give the under-source homotopy.

For ordinary uniqueness, `classicalCWHomotopyCancel` constructs the canonical
self-cylinder of `f`. Its fold, leg equivalence and actual homotopy descent
cancel precomposition into any same-universe topological target `Y`:
a homotopy between `h₀ ∘ f` and `h₁ ∘ f` gives one between `h₀` and `h₁`.
`homotopic_classicalCWComparisons` applies this to two under-source witnesses.
The result is ordinary homotopy of comparison maps; it does not assert
coherence relative to the prescribed under-source homotopies or basepoint
tracks, a strictly pointed inverse, or a natural chosen inverse.

## Explicit universe transport

[`CommonUniverseChains`](../LocalCoefficients/CommonUniverseChains.lean)
and [`PlusConstruction.CommonUniverse`](CommonUniverse.lean)
prove transport for a source in `Type u`, a target in `Type v` and an auxiliary
universe `w`, with `U = max u v w`. The original certificate must already
quantify all target coefficient systems in `U`:
`IsPlusConstruction.{u,v,U} f γ N` yields an
`IsPlusConstruction.{U,U,U}` certificate on the explicit ULift spaces.
The map is literally `up ∘ f ∘ down`, the track is `up ∘ γ`, and the subgroup
is the image of the original `N` under the actual based Pi-one equivalence.
The chain retract square uses the original chain map; it does not assume
large coefficient systems are small or enlarge a smaller coefficient
quantifier. Projecting back recovers the original forward map and every time
of the original track.

The separately proved geometric owners construct
`ClassicalCW.subtypeCWComplex C c`, `uliftCWComplex`, and
`uliftSubtypeCWComplex C c`. For the intrinsic subtype, the supplied `c : C`
sets only irrelevant characteristic-map values outside the closed disks;
the whole original closed-disk map and inverse chart are retained. Hausdorff
closedness supplies the intrinsic weak topology. Direct ULift uses literal
up/down charts and lifted cell indices, with no additional Hausdorff premise.
The combined subtype/ULift construction keeps its Hausdorff and explicit-point
inputs and preserves original source balls, closed-disk values and inverse
charts. There is no countability, local finiteness, finite-dimensionality or
supplied homeomorphism-transport certificate.

## Mixed-universe uniqueness on the original spaces

[`IsPlusConstruction.classicalCWPlusUnique_commonUniverse`](ClassicalCWUniquenessUniverseLift.lean)
takes actual Hausdorff CW subtypes `A`, `B`, `C` with ambient universes `u`,
`v`, `w`. For `U = max u v w z`, it requires the original certificates
`IsPlusConstruction.{u,v,U} f γ N` and
`IsPlusConstruction.{u,w,U} g δ N`, quantifying all target local systems in
`U`. It returns a homotopy equivalence between the original `B` and `C`,
a homotopy between the original `h ∘ f` and `g`, and ordinary uniqueness of
every continuous comparison `k` with the required precomposition homotopy.
No larger coefficient quantifier is inferred from a smaller one.

`classicalCWPlusUnique_successor` specializes this to original `A : Type u`
and `B`, `C : Type (u + 1)`, consuming the literal original
`IsPlusConstruction.{u,u+1,u+1}` certificates. The original maps, points,
tracks and common subgroup are retained as inputs. No cover, lift, cylinder,
domination, CW-transport certificate or desired equivalence is supplied.

The assembly constructs intrinsic subtype and ULift CW geometry and transports
the based certificates. [`UnivSubtype`](UnivSubtype.lean)
uses canonical `Set.univ` homeomorphisms, retaining each original track time,
the nonabelian based Pi-one square, actual kernel and subgroup, and original
chain maps. After applying the same-universe theorem, canonical homeomorphisms
return the equivalence and under-source homotopy to the original spaces;
the homotopy endpoints are definitionally the original composites.

`classicalCWHomotopyCancelCommonUniverse` also returns ordinary cancellation
into an arbitrary original `Y : Type w` under the displayed coefficient
bound. It adds no CW, connectedness or separation condition on `Y`.
The comparison theorem retains actual Hausdorff CW hypotheses on `A`, `B`,
`C`, with no finite-dimensional, countable or locally finite restriction.
It supplies neither prescribed-track coherent uniqueness nor arbitrary
CW-homotopy-type transport. The original ring-plus certificate and Q comparison
retain the separate scope recorded in the [ring plus guide](../../KTheory/Plus/README.md).

## Clients and scope

The independent [automatic client](../../../examples/downstream/Consumer/ClassicalCWPlusAutomatic.lean)
and [tests](../../../QuillenTest/ClassicalCWPlusAutomatic.lean) retain the original
maps, points, tracks, subgroup and common-universe certificates.
The [chosen-cover client](../../../examples/downstream/Consumer/ClassicalCWPlus.lean)
keeps its explicit geometric inputs. The
[CW-cover client](../../../examples/downstream/Consumer/CWSimplyConnectedCover.lean),
[path-class client](../../../examples/downstream/Consumer/PathClassUniversality.lean),
[common-universe client](../../../examples/downstream/Consumer/CommonUniversePlus.lean),
and [CW-universe client](../../../examples/downstream/Consumer/CWUniverseTransport.lean)
exercise the separate constructions and equations. The
[mixed-universe client](../../../examples/downstream/Consumer/ClassicalCWPlusMixedUniverse.lean)
and [tests](../../../QuillenTest/ClassicalCWPlusMixedUniverse.lean) check the original
successor certificates, cancellation endpoints and pointwise transport laws.

See [homotopy foundations](../README.md) for the homological and
metric tools, [API](../../../docs/reference/API.md) for focused imports, and
[scope](../../../docs/reference/Scope.md) for collective boundaries and verification scope.
