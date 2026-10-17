# Thomason–Trobaugh continuation handoff

Current handoff: the selected archive on baseline
`492454b306a1a1a26d5701d0503f5aaf127b9367`, integrated with the unchanged pins.
The projective-line P1–P5 phase and constructed fine localization are preserved.
The fine transition range, original-group telescope comparisons and fixed
nonpositive localization sequence now have their stated scope below. Classical
Thomason–Trobaugh identification remains open. Source correspondence, ordinary
review and current validation are separated in
[the integration evidence](evidence/TTFineCompletionAndRawPasting.json).

## Objective and handoff boundary

The remaining objective is classical TT Theorem 7.4: for qcqs `X`, a
quasi-compact open `U`, and `Y = X − U`, identify the original classical
nonconnective objects and prove the canonical fiber sequence

```text
Kᴮ(X on Y) → Kᴮ(X) → Kᴮ(U).
```

The auxiliary-support version uses a closed support `Z` whose complement is
quasi-compact and retains the original support enlargement, restriction,
whole nullhomotopy and signed boundary. The already constructed section
completion has these localization comparisons. Its identification with the
classical objects is a separate mathematical obligation. Preservation of the
original negative and nonnegative groups in the actual fine completion is now
supplied for qcqs ambient schemes, with compact removed open for the supported
telescope and localization sequence.

A receiving assignment should select an exact remaining consumer below and
retain its original maps, conditions and evidence boundary. This handoff does
not itself record the result of a commit or push.

## Projective-line phase

Let `P` be the original native projective line over `X`, with projection `p`
and original tautological line `L = O(-1)`. The forward functor is the existing
two-summand map, with its original product coordinates:

```text
Φ(A,B) = p^* A ⊕ (L LEFT tensor p^* B).
G(E)   = (Rp_* E, Rp_*(E RIGHT tensor L)[1]).
```

The exact original flasque model implements the actual Godement totalizations,
ordinary direct images, chosen zero objects and signed shifts. Derived
categories supply homological comparisons; the K-theory endpoints are the
actual Waldhausen models. A derived-category equivalence of the two-summand
functor is neither assumed nor generally true.
The local implementation uses direct arbitrary-ring diagonal generation;
the [projective-line route](TTLocalization.md#p-prove-the-necessary-projective-line-k-equivalence-b1)
records its relation to TT's noetherian-reduction proof.

| Phase | Available result | Entry owner |
| --- | --- | --- |
| P1 | Original canonical tensor/pullback mates and determinant contractions, with both chart signs fixed | [LineTensorCompatibility](../../Quillen/AlgebraicGeometry/Scheme/ProjectiveLine/LineTensorCompatibility.lean), [PullbackTensorCompatibility](../../Quillen/AlgebraicGeometry/Scheme/ProjectiveLine/PullbackTensorCompatibility.lean) |
| P2 | Genuine QC/strict representatives and perfection of the original derived projection for every intrinsic-perfect D+ input over every commutative ring, including zero | [QuasicoherentRepresentative](../../Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/QuasicoherentRepresentative.lean), [IntrinsicPerfectPushforward](../../Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/IntrinsicPerfectPushforward.lean) |
| P3 | Natural diagonal generation on the actual affine two-chart line, retaining original roofs, endpoints, units and perfect coefficients | [OriginalPerfectGeneration](../../Quillen/AlgebraicGeometry/Scheme/ProjectiveLine/OriginalPerfectGeneration.lean) |
| P4 | Both original affine model K-map inverse laws and bijectivity of the unchanged native map, for all `n : ℕ`, including zero | [FlasqueGPhiMatrix](../../Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/FlasqueGPhiMatrix.lean), [FlasquePhiInverse](../../Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/FlasquePhiInverse.lean), [FlasqueNativePhiTransport](../../Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/FlasqueNativePhiTransport.lean) |
| P5 | Both actual original qcqs model inverse laws, identification of geometric G with the unchanged native inverse, and the original compact-open supported Phi bijection | [P5NativeGlobalInverse](../../Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/P5NativeGlobalInverse.lean), [NativeGlobalBundle](../../Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/NativeGlobalBundle.lean), [NativeGlobalSupport](../../Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/NativeGlobalSupport.lean) |

[P5PositiveUnitNative](../../Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/P5PositiveUnitNative.lean)
proves that the actual canonical unit `A → p_*T(p^* A)` is weak on every
native quasi-compact base and that its literal K-map is identity.
[P5NativeGPhiLaw](../../Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/P5NativeGPhiLaw.lean)
combines this unit with negative vanishing and signed Euler additivity to
prove the original `GΦ = id`, without assuming Phi bijectivity.
`P5NativeGlobalPhi` transports the already proved native qcqs Phi
bijection through the actual model inclusions. `P5NativeGlobalInverse`
then proves `ΦG = id` and identifies the actual geometric G with
`nativeGlobalTwoSummandKEquiv.symm`. The original forward map and
`Product.KEquiv` are unchanged.

Global projection perfection and the exact coefficients require a
quasi-compact base. The coefficient and Phi support-preservation statements
hold for every base open. Native global K-bijectivity additionally requires
quasi-separatedness; the supported bijection uses compact base opens. All
natural degrees include zero. Arbitrary-base-map naturality, the general
projective-bundle formula, Proj/twisting-sheaf identification, and the older
specialized P3 endpoint-unit/connecting comparisons retain separate scope.

## Preserved downstream results

The original H0/H1/M/Q family and scalar-cube filler have been independently
reviewed and canonically checked. Start from
`BoundedFlat/MWholeCubeConsumers`, `MWholeNativeCube`, `MWholeNative`, and
`MWholeScalarFaces`. They retain the original six faces, twelve whole edges,
basepoints, level zero, original Laurent inclusion and independent
homotopy/loop/structure times. The generic filler is owned by
`Topology/Realization/SimplexCubeExtension` and `SimplexCubeFaces`. These are
actual finite-stage coherence results; they do not by themselves prove the
whole raw iterate/telescope comparison or identify the classical seed.
The separate actual six-face unit cube is also constructed by
`BoundedFlat/CoefficientBassUnitNativeCube.interiorCube`. Its
`CoefficientBassUnitCubeConsumers` gives the whole comparison, cone identity
and parameter-looped `stepIdentity`, with no caller-supplied filler.

The positive Bass row is proved on `K_m(S) := PerfectK(Spec S, m)` for every
commutative ring, including zero, and every `n ≥ 0`:

```text
1 → K_(n+1)(R) → K_(n+1)(R[T])²
  → K_(n+1)(R[T,T^-1]) → K_n(R) → 1.
```

Its chart map is the actual positive restriction times inverse negative
restriction. Its terminal map is the first O-coordinate of the same native
Phi inverse after the original T-first Mayer–Vietoris boundary. The
connecting coefficient image is exactly `(a,a⁻¹)`. The polynomial zero
evaluation supplies the actual retraction without assuming that the zero
section is flat. Owners: `ProjectiveLine/BassPositiveCharts`,
`BassPositiveMayerVietoris`, and `BassPositiveFundamental`. This proves
exactness and terminal surjectivity, including `K₁ → K₀`; it does not yet
compute that terminal map on `[T]`, split the Laurent quotient, identify
classical ring K-theory, remove Nil terms, or prove homotopy invariance.

Four frozen relative scalar-boundary leaves compute the original normalized
forward scalar class under the original relative localization boundary as
the actual supported cofiber object class. The relative sign is positive
because two separately proved inversions cancel. The canonical target owner
is `PerfectComplexes/ScalarForwardRelativeBoundary`, with generic topology
at `HomotopyFiber/LoopComponentTransport` and `ConnectingLoopPathClass` and
the actual cofiber component at `PerfectComplexes/ScalarCofiberFiberComponent`.
The theorem is
`Quillen.BassLaurentUnitBoundary.scalar_forward_changeWeak_boundary`.
Independent complex ordinary review and canonical native checks accept this
relative theorem. The fine Laurent positive Bass boundary and its final
O/O(-1) sign remain open.

The actual fine stage-i transitions and inclusions are isomorphisms in each
degree `d ≥ -i`, including the bottom degree, for qcqs ambient schemes.
For supported towers the removed open is compact. The original negative-group
comparison is exactly the finite-bottom comparison followed by the original
inclusion; the connective comparison uses original evaluation and stage zero.
All are natural on the full coefficient category and retain the Laurent
quotient. The supported negative/connective zero maps agree, and original
support forgetting commutes with these comparisons. The finite-bottom
supported comparison and forget square require only compact ambient scheme.
Entry owners are `CoefficientBassFineRangeInvertibility`,
`CoefficientBassFineTelescopeComparison`, `CoefficientBassConnectiveTelescopeComparison`
and their supported counterparts.

`CoefficientFullOpenBassRestriction` proves the full-open fine row, action,
seed and telescope definitionally the ambient constructions on the open scheme,
and the localization map equals original scheme restriction on every cylinder
using only the open immersion. `Bass/SupportedLocalizationExactness` and
`Bass/SupportedLocalizationBoundary` give the recurring original nonpositive
sequence for compact removed open in a qcqs ambient scheme. Its boundary is
the fixed signed same-null fine boundary. The existing geometric positive
K₁-to-supported-K₀ boundary joins by exactness at literal K₀ groups; its equality
with the fine boundary and arbitrary-pair boundary naturality remain open.

The reusable raw descent is `Topology/Prespectrum/PushoutConeFamily` and
`PushoutConeFamilyRecovery`: it retains complete supplied families under
parameter restriction and independent looping. The actual Laurent and both
polynomial native cells now lie in the original full target cone. The selected
polynomial three-cube has all six scalar faces, its original eighteen-node
Laurent bottom and unreduced tip, based values and independent structure time.
`CoefficientBassRaw1PolynomialNativeAttachments` proves both whole height-zero
faces equal to the Laurent family after the actual source chart maps. The
remaining overlap four-cube and complete L/P/O attachments are distinct from
these supplied polynomial faces.

## Recommended next assignments

1. **Finish the original Laurent `[T]` terminal boundary and splitting.**
   Transport the relative scalar theorem through the actual
   [`perfectAcyclicSupportedKEquiv`](../../Quillen/AlgebraicGeometry/PerfectComplexes/OpenSupport.lean)
   and [`qcqsPerfectConnectingHom_comp_relative`](../../Quillen/AlgebraicGeometry/PerfectComplexes/GlobalLocalization.lean).
   Use the existing
   [`Quillen.PerfectComplexes.polynomialScalarForwardKOneClass_restrict_rankOne`](../../Quillen/AlgebraicGeometry/PerfectComplexes/ScalarLaurentClassComparison.lean)
   to identify the original forward class with the intrinsic automorphism
   class of `laurentGlobalUnit`; retain its actual restriction rebase.
   The positive Bass map uses lower negative-chart localization. Prove the
   relation of that chart's scalar to `T⁻¹`, the corresponding unit-class
   inversion, and the original global supported cone of
   `tautologicalLineInclusion ≫ prod.fst`. Its original positive
   trivialization and negative polynomial-coordinate formula must give the
   actual O/O(-1) class. Transport through original excision and the same
   native Phi inverse. Exactness or the relative positive sign alone does
   not determine the terminal sign. Acceptance: for every commutative R,
   including zero, and every `n ≥ 0`, compute the terminal boundary on the
   actual original `[T]` operation applied to `x : PerfectK(Spec R,n)`.
   Prove explicitly whether the original sign gives `x` or `x⁻¹`, using
   the same T-first charts and signed O/O(-1) class calculation. Construct
   the resulting section `s_n` of that literal terminal map, with
   `∂_(n+1) ∘ s_n = id`, and prove naturality in ring/coefficient arrows.
   Retain the original `[T]` operation and its proved sign, including
   `K₁ → K₀`; keep Nil contributions in the chart quotient.

2. **Assemble the original raw second-projection cells.**
   Reuse the actual identity/composition cubes, Laurent native cell,
   polynomial native cells and their entire height-zero attachments. Construct
   the overlap O four-cube with comparison, route, cone-height and overlap
   coordinates. Retain all eight three-faces and whole chosen earlier fillers;
   verify their intersections, including the original half-height midpoint,
   and every quotient attachment. Assemble `PushoutConeFamily (I × I)`, recover
   both entire cone routes and loop to actual `PlusPasting`/`MinusPasting` for
   `CoefficientBassSecondCoefficientProjection`. Retain genuine arbitrary
   polynomial/Laurent input domains, reference isomorphisms, unreduced tips,
   based values and independent clocks. Then prove second-stage
   identity/composition and whole seed naturality, and extend to all raw stages.
   Acceptance is the actual original comparison with each specified whole
   prior filler retained. The chosen-chart augmentation preserves all four
   sides of the earlier chart square; `CoefficientBassSeedChosenSquareRange`
   preserves a supplied range condition and leaves the concrete boundary-range
   proof as a separate obligation.

3. **Identify original boundaries and auxiliary group diagrams.**
   Reuse the proved fine transition range and canonical original telescope
   legs; they are not remaining obligations. Prove arbitrary-pair naturality
   of the transported negative boundary and identify it with the original
   geometric boundary through the actual stable/K connecting compatibility.
   `Bass/SupportedEnlargement` already supplies original enlargement maps,
   their identity/composition and forget compatibility. Identify those maps
   and original restrictions with the T, T∪U and T∩U auxiliary section towers
   and their exact localization diagram. Retain qcqs ambient, compact removed
   open, and compact auxiliary acyclicity open for the final auxiliary fine
   comparison. Neither the existence of an enlargement map nor exactness at
   literal K₀ by itself supplies the required whole-null boundary square.



The final B3 task identifies the original raw classical model and transports
the same-null auxiliary-support diagram. It must retain the three actual
acyclicity opens `U∪T`, `T`, `U∩T`, with `T = X−Z`, and the original signed
boundary. The constructed completion must not simply be renamed `Kᴮ`.

## Entry and reproduction

Use [the maintained TT roadmap](TTLocalization.md) for exact remaining
dependencies and [scope](../reference/Scope.md) for mathematical boundaries.
Read only the owners needed by the next assignment. In the original parent
research workspace, follow its locator-first research entry and current
execution/formalization/review contracts; reconcile recovered claims with
the live worktree. In a standalone clone, follow
[CONTRIBUTING](../../CONTRIBUTING.md).

Use the active standalone Quillen checkout selected by the receiving task.
The mathematical source identity is the baseline and selected source recorded
above; a scratch path or a historical checkout location is not its authority.
Keep changes outside the assigned consumer read-only.

The source integration uses Lean **4.34.1** and mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Keep the committed pins. For a
fresh source build, choose the exact needed module, for example:

```sh
lake build Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeGlobalBundle
lake build Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.BassPositiveFundamental
lake build Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeCubeConsumers
lake build Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedFineTelescopeComparison
lake build Quillen.AlgebraicGeometry.PerfectComplexes.Bass.SupportedLocalizationBoundary
lake build Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialNativeAttachments
python3 scripts/generate_imports.py --check
python3 scripts/check_library_layout.py
```

The handoff's native checks are scoped builds, meaningful typed consumers,
style and complete defining-origin kernel/foundation audits of the new
families, plus exact reuse of unchanged pinned dependencies. They are not a
fresh whole-library proof replay. Preserve source, module origin, actual
compiler options, logs and all six output companions when reusing local
coverage. A partial `Quillen` prefix can shadow later search roots: use a
coherent complete first-hit closure. Do not copy compiled artifacts into
the committed handoff.

Same-host compiled artifacts are optional acceleration. Reuse requires matching
source, pins, outputs and a coherent first-hit module closure; the historical
compiler path or a result JSON alone does not reconstruct a dependency snapshot.
The current source-only integration deliberately excludes archived binaries
and unvalidated drafts. A standalone clone builds from committed source.

Final classical closure has the separate full-library boundary:

```sh
bash scripts/check.sh --rehash
```

That pipeline includes the maintained tests, downstream client and both
explicit foundation audits. Green checks do not close an absent mathematical
comparison. Independent ordinary review of new load-bearing mathematics and
its actual consumers is required; established-status assignment has its
separate stronger review gate.

## Checkpoint and evidence

The current archive starts from `492454b306a1a1a26d5701d0503f5aaf127b9367`.
Use the delivered repository history to resolve subsequent integration commits;
this handoff makes no push or release assertion. The new
[fine completion and raw-pasting evidence](evidence/TTFineCompletionAndRawPasting.json)
records the selected source identity, exclusions, ordinary review coverage,
historical evidence limits and current affected-scope validation.

The compact [continuation checks](evidence/TTContinuationChecks.json) and
[Bass cube evidence](evidence/TTBassCube.json) identify delivered relative
source paths/hashes, independent reviews, pins and actual checked coverage.
Historical source-only HEAD observations, original compiler bases, failed
probes and source-format/server-only aliases remain distinct. Scratch is
an optional same-host acceleration, not the source of an unrecorded theorem
or a required remote input.
