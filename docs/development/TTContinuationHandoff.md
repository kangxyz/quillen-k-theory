# Thomason–Trobaugh continuation handoff

Prepared on 2026-10-15 for another agent to continue after P1–P5. The
projective-line phase is complete at the scope below. Classical
Thomason–Trobaugh localization still has the remaining comparisons listed
here. The delivery checkpoint is the Git commit containing this document;
the actual push result is reported in the accompanying task response.

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
classical objects and preservation of their original nonnegative groups are
separate mathematical obligations.

The user asked to finish P1–P5, commit and push, and hand subsequent work to
other agents. The current thread stops at this checkpoint; a receiving
agent can use the assignments below when asked to continue. Existing
downstream results are preserved at their stated scope.

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
The separate six-face **unit/identity** cube remains open; the completed
cube proves composition.

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

2. **Use the fixed cube for the original raw seed/iterate comparison.**
   Consume `MWholeCubeConsumers` rather than rebuilding M or requesting a
   caller-supplied composition cube. Construct the separate unit cube
   required by `CoefficientBassUnitInteriorCube`, retaining the already
   proved polynomial-span unit and both original Laurent chart unit
   squares. Extend the actual normalized fine-to-raw chart
   comparison, original cone/source-null/one-step seed, raw iteration and
   telescope comparison to the ambient, open and auxiliary-supported rows
   needed by the final diagram. Preserve the original Laurent tracks,
   zeros and independent coordinates. Acceptance: the actual comparison
   commutes with the original seeds and stage/telescope inclusions, not
   merely with an abstract isomorphic spectrum.

3. **Advance the original groups and lowest transitions.**
   Follow B2-C/G in the maintained roadmap. Prove recursive chart middle
   exactness with mixed polynomial/Laurent variables and the original
   quotient maps. The positive splitting is a prerequisite; right
   exactness alone is insufficient. Extend original negative-group
   comparisons through support forget/enlargement and scheme/open maps.
   Then prove B2-D's actual initial seed, B2-E's transition in the boundary
   degree `d = −i`, and B2-F's original stage-i colimit leg. Stability only
   from stage `i+1` does not prove the required canonical leg.

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

The original delivery checkout is the independent Git repository at
`tmp/output/quillen-library-release/quillen-k-theory` inside the parent
research workspace. Run library Git commands from this checkout. The parent
workspace also has separately owned elliptic-integral notes and bibliography
changes; those are outside this handoff's staging and push scope.

The source integration uses Lean **4.34.1** and mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Keep the committed pins. For a
fresh source build, choose the exact needed module, for example:

```sh
lake build Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeGlobalBundle
lake build Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.BassPositiveFundamental
lake build Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeCubeConsumers
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

For optional same-host acceleration, the final checked descriptor is
`/private/tmp/r5-investigations/quillen-tt-resume3-20261014/p5_final_inverse_admission/runtime.json`
(SHA-256 `4ed8856972b4e9a290dde8cf0d604f769a753741a903a00d821667c763d8f687`).
Its sibling `final-ready-guard.json`, `sources.json` and `actual-input-basis.json`
locate the exact outputs and checks. Reuse requires matching source, pins,
outputs and first-hit routing. The descriptor retains its check-time
source-only HEAD; the final Git commit alone does not change identical
compiled source bytes. A standalone clone builds from the committed source.

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

Earlier local checkpoints are `9dcb8112` (P3/foundations), `41e7da1f`
(original affine GPhi and exact additivity prerequisites), `ecd519b3`
(both original affine inverses), `6b41b95d` (native coefficients/support),
and `a364b7f7` (original qcqs/support Phi bijections). The commit containing
this handoff adds the final P5 inverse sources, preserved downstream
source and updated scope. Use `git log -1 -- docs/development/TTContinuationHandoff.md`
to resolve its exact identity in the delivered checkout.

The compact [continuation checks](evidence/TTContinuationChecks.json) and
[Bass cube evidence](evidence/TTBassCube.json) identify delivered relative
source paths/hashes, independent reviews, pins and actual checked coverage.
Historical source-only HEAD observations, original compiler bases, failed
probes and source-format/server-only aliases remain distinct. Scratch is
an optional same-host acceleration, not the source of an unrecorded theorem
or a required remote input.
