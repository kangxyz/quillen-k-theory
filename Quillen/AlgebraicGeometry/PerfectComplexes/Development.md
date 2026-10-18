# Thomason–Trobaugh comparison boundaries

The constructed section completion and native current-stage localization have proved comparisons. Their identification with a specified classical Thomason–Trobaugh spectrum and its original null diagram remains open. This guide records that boundary and the separate raw-cell route; it does not rename a constructed completion as classical Kᴮ.

## Classical target and source

For qcqs `X`, an open immersion `j : U → X` with quasi-compact `U`, and `Y = X − U`, the classical target is the canonical fiber sequence

```text
Kᴮ(X on Y) → Kᴮ(X) → Kᴮ(U).
```

For a closed auxiliary support `Z` with quasi-compact complement, its supported form is

```text
Kᴮ(X on Y ∩ Z) → Kᴮ(X on Z) → Kᴮ(U on U ∩ Z).
```

R. W. Thomason and T. Trobaugh, *Higher Algebraic K-Theory of Schemes and of Derived Categories*, The Grothendieck Festschrift III, Progress in Mathematics 88 (1990), 247–435, Theorem 7.4, printed pp. 365–366; §§6.4, 6.6(a), 7.0, 7.5(a) retain the initial comparison for every `n ≥ 0`, including zero. [DOI](https://doi.org/10.1007/978-0-8176-4576-2_10); [original paper](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/Thomason-Trobaugh.pdf).

## Constructed results and their conditions

[Connective localization](Localization.md) identifies the canonical relative/open endpoint in positive degrees, is injective at zero, and preserves the actual K₀ image and original boundary. [Auxiliary support](SupportedOpen/README.md) supplies naturality, excision, and connective Mayer–Vietoris.

[Bounded-flat section comparisons](BoundedFlat/BassComparison.md) give the actual fine transition and inclusion range `d ≥ -i`, with the original finite-bottom comparison followed by the original inclusion. Ambient schemes are qcqs; supported completion additionally requires compact removed open. Nonnegative comparisons use original evaluation and stage zero. These are identifications with the constructed fine completion.

The native current-stage map `ParameterFullCurrentNull.currentLift f (op integerBase)` is stable in every signed degree for an open immersion `f : P ⟶ Q`, compact `P,Q`, and quasi-separated `Q`. The stable route `I → T ← N ← C` preserves support forgetting, full-open restriction, and every value of the selected null. The original current-stage scalar seed is retained. No generic equivariance premise remains at this endpoint.

The [projective-line K-equivalences](ProjectiveLine/README.md) retain the existing two-summand map, exact geometric coefficients, both affine and native qcqs inverse laws, and compact-open supported bijectivity in every natural degree, including zero. These facts do not identify classical Kᴮ.

## Original Laurent boundary and splitting

The positive Bass row for `K_m(S) := PerfectK(Spec S,m)` is exact for every commutative ring, including zero, and every `n ≥ 0`, including K₁ to K₀. Its chart difference is positive restriction times inverse negative restriction. Its terminal arrow uses the first O-coordinate of the same native Phi inverse after the original T-first Mayer–Vietoris boundary. The relative scalar-to-supported-cofiber theorem has positive sign because two proved inversions cancel.

The fine Laurent `[T]` terminal formula and its actual O/O(-1) zero-locus class remain open. The lower negative-chart scalar must be related to `T⁻¹`, its unit class inverted, and the original supported cone of `tautologicalLineInclusion ≫ prod.fst` compared through its positive trivialization and negative polynomial coordinate. Transport through original excision and the same native Phi inverse must determine whether the original operation gives `x` or `x⁻¹`. A natural section of the literal terminal arrow, with its proved sign, remains to be constructed. Exactness and the relative positive sign alone do not determine it. Keep all Nil contributions; classical ring-K identification, Nil vanishing, and homotopy invariance are separate.


## Original raw-cell route

This subsection retains the older raw-cell comparison target: the actual
bounded-flat/perfect geometric Bass construction, with its chosen pullbacks,
original normalization/composition tracks and independent comparison, loop and
structure coordinates. The strict fine section tower cannot be substituted
for that target. The native current-stage theorem above follows another
route and does not require this O-cell producer. If the raw route is used
for classical identification, its full stated correspondence is still needed.

| Interface | Available result and precise remaining consumer |
| --- | --- |
| E2-C/N/S/W: original one-step evaluation | `CoefficientSectionEvaluationComposition`, `CoefficientSectionEvaluationTopology` and `CoefficientSectionEvaluationSeedComparison` construct the normalized composition equation, both chart faces and moving cylinder, original source-null pasting, whole one-step seed homotopy and levelwise weak cone evaluation. No caller-supplied coherence, openness, compactness or flatness is added to these native identities. Perfect/stable comparisons retain their separate hypotheses. |
| Raw1 composition | `MWholeNativeCube` constructs the six original composition faces with twelve whole edges, basepoints, level-zero loops and independent structure time. `MWholeCubeConsumers` gives the original comparison, cone and parameter-looped step composition with its literal Laurent inclusion track. |
| Raw1 identity | `CoefficientBassUnitNativeCube.interiorCube` constructs the actual six-face original identity cube. `CoefficientBassUnitCubeConsumers` gives the whole comparison square, cone identity and `stepIdentity`; no unit filler remains to be supplied. |
| Objectwise second stage | `CoefficientBassActualSeedComparison.comparison` descends both actual mixed fillers to the original two-chart seed square. `CoefficientBassSeedIteration.stepMap` is its objectwise first-to-second parameter-looped map, with literal inclusion, cylinder and output-loop formulas. |
| Fixed chosen faces | The seed-carrier, chosen-cube and chosen-chart augmentation owners preserve earlier selected cubes, their entire chart squares, whole reference nodes and original clocks. `CoefficientBassSeedChosenSquareRange` preserves a supplied range condition; it does not prove the concrete chosen-boundary range. No functorial extension choice or recursive carrier for arbitrary raw cell trees is asserted. |
| Parameterized original quotient descent | `Topology.Prespectrum.PushoutConeFamily` accepts four typed L/P+/P−/O families with their quotient attachments, based values and independent structure laws. For any locally compact external parameter it descends the original pushout and reduced cone, commutes strictly with parameter restriction and then loops independently. `PushoutConeFamilyRecovery.ofFamily_desc` recovers the complete supplied family. `CoefficientBassCompositionCellDescent` recovers the original M cone/step composition. |
| Laurent and polynomial source cells | `CoefficientBassRaw1LaurentFamily` gives both entire Laurent relative comparisons. `CoefficientBassRaw1PolynomialCommonPasting` pastes three original cap cubes; its Sides, LaurentFace and Top owners supply all six scalar faces, including the unchanged eighteen-node Laurent bottom and original unreduced tip. `CoefficientBassRaw1PolynomialCommonPastingNative` retains arbitrary genuine polynomial input, based values and independent structure time. |
| Native target and lower attachments | `CoefficientBassRaw1LaurentNativeCell.family` and `CoefficientBassRaw1PolynomialNativeCells.plus/minus` are jointly continuous families into the full original target Bass cone. The polynomial cells have the original top, based and structure laws. `CoefficientBassRaw1PolynomialNativeAttachments.plus_zero/minus_zero` identifies each entire height-zero face with the Laurent family after the actual source chart map, independently of the target chart. |
| E2-I: remaining raw producer | Construct the O family with comparison, route, cone-height and overlap coordinates, all eight prescribed three-faces and whole intersections including the original half-height midpoint. Retain chosen old fillers and all L/P/O quotient attachments; assemble `PushoutConeFamily (I × I)`, recover both entire cone routes and loop to actual `PlusPasting`/`MinusPasting` for `CoefficientBassSecondCoefficientProjection`. Then supply second-stage identity/composition and full coefficient naturality of the seed before producing all raw stages and transition homotopies. |
| E2-T: remaining telescope comparison | From actual stage comparisons `E_n` and whole transition homotopies `J_n`, use `Telescope.mapOfHomotopies` and its T1 stable-equivalence theorem. Retain stage/initial/cylinder formulas, coefficient and restriction squares and the same-null signed boundary comparison. |

The one-step normalized composition uses actual evaluation maps `e_i`,
section reindexing `S_f`, geometric pullback `P_f`, evaluation isomorphism
`κ_f` and original normalized composition `β(f,g)`. Its component equation is

```text
κ_(f≫g)(x); β(f,g)(E_i x)
  = transportS(x); κ_g(S_f x); P_g(κ_f(x)).
```

`transportS` is the actual strict section-reindexing composition equality.
The cone/null/seed comparison retains both normalization choices and the
original geometric split track. Its whole loop-coordinate equation uses
independent comparison, loop and structure times. The constructed fine
initial seed is now connective-invertible under qcqs hypotheses; this does
not imply an all-stage raw producer.

The composition geometry is built from `SplitTripleSimplex` and
`TripleNativeEvaluation`, the common 18-node original double-square rectangle,
the shared H0/chart/bottom families, and `MWholeNative`'s actual 139-simplex.
Their chosen triangles, twelve whole shared edges, chart pauses and continuous
three-side collapse remain unchanged. The generic finite scalar extension is
owned by `SimplexCubeExtension` and `SimplexCubeFaces`. The separate unit
construction uses its own original faces and scalar extension. Recorded cube and source-cell evidence is in the
[global evidence registry](../../../docs/evidence/README.md#recorded-source-cell-scope).

The current polynomial cube has complete scalar intersections; these must not
be listed as unproved. The unresolved higher overlap boundary is a different
object. The generic descent does not construct its geometric attachments,
and equality after native evaluation does not imply equality of the dependent
scalar reference nodes. Contractibility cannot repair an unclosed prescribed
boundary or replace a previously chosen whole filler. Retain genuine Laurent
and polynomial input domains rather than replacing them by images of the
common corner.

`strictDiagramIterate` requires a literal prespectrum-valued functor and
strict transformations. The raw maps have prescribed homotopy identity and
composition laws. This API cannot be applied directly to them to declare a
functorial raw second stage. A proposed induction on source-cell depth and
finite coefficient words remains a proof plan; no well-founded recursive
coherence theorem is asserted for that cell producer. A classical
identification through E2 must cover every ambient, open and
auxiliary-supported row required by its final diagram. This remaining
raw-cell work does not retract the native current-stage theorem above.

## Classical object and same-null correspondence

Specify the classical model by the original raw perfect/bounded-flat-perfect
spectrum, native polynomial/Laurent squares, original cone/loop stages and
forward Laurent transitions, followed by their homotopy colimit (TT 6.4).
If an ordinary colimit is used, prove its cofibration-replacement comparison.
A proposed classical identification must produce the actual all-stage
comparison to this model, either from the native current-stage construction
or through the separate E2 raw-cell route. The integer-parameter Model
projection isomorphisms alone do not establish that comparison. B2's original
class maps must agree with the selected spectrum maps in every nonnegative
and negative degree.

For T=X−Z and Y=X−U, compare the whole G7 null diagram with the specified
classical diagram
on (X,Y∩Z), (X,Z), (U,U∩Z). Their acyclicity opens are U∪T, T, U∩T.
Under qcqs X and quasi-compact U,T, construct all three stable comparison
maps, the original support-enlargement/restriction squares, and coherence with
the same whole canonical null. Then transport the actual stable fiber lift
and prove, in each signed degree, the original boundary equation

```text
c_support,(n−1) ∘ boundary_section
  = boundary_classical ∘ c_open,n.
```

The classical boundary is the boundary of the specified classical null diagram;
defining a conjugate boundary without identifying it does not close B3.
Obtain the basic sequence by Z=X. State the library's actual stable
fiber-sequence notion; all-signed stability is not a levelwise homotopy
equivalence claim. This final milestone requires the accepted classical
object/seed/null correspondence, G7's auxiliary support diagram and B2's
original-group comparison, with no remaining target-specific localization
hypothesis. The new basic-pair current-stage theorem does not by itself
supply that auxiliary-support or signed-boundary transport.

## Declaration locators

These additional names use the same objects, hypotheses, and original maps as the linked construction sections. They are locators within those interfaces, not stronger comparison statements.

| Declaration / module | Construction and conditions |
| --- | --- |
| `MWholeScalarFaces` | [Constructed results and their conditions](#constructed-results-and-their-conditions) |
| `ConnectingLoopPathClass`, `Quillen.BassLaurentUnitBoundary.scalar_forward_changeWeak_boundary` | [Constructed results and their conditions](#constructed-results-and-their-conditions) |
| `perfectAcyclicSupportedKEquiv`, `qcqsPerfectConnectingHom_comp_relative`, `Quillen.PerfectComplexes.polynomialScalarForwardKOneClass_restrict_rankOne`, `laurentGlobalUnit` | [Original Laurent boundary and splitting](#original-laurent-boundary-and-splitting) |

Source and validation records are in the [global evidence registry](../../../docs/evidence/README.md).
