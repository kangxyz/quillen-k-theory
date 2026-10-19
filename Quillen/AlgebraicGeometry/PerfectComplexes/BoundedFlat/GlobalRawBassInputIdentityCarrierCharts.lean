/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputIdentityNodes
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputIdentityCharts
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCubeExtension

/-!
# Three actual common-reference faces of the global raw identity boundary

The original input surface and both full original unit-square chart surfaces take values in
the same nerve of complete dependent reference nodes. Their compact evaluations recover every
original native level at its unchanged two-coordinate parameter. No cube or whole identity
square is asserted.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Convexity
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.GlobalRawBass.InputIdentityCarrierCharts
open InputIdentityNodes

private theorem pre_family {V W T : Model.{u}} {k : ℕ}
    (F : V ⟶ T) (J : V ⟶ W) (G : W ⟶ T) (δ : F.functor ≅ (J ≫ G).functor)
    (N : Fin (k + 1) → CommonReferenceNerve.Node G) :
    ModelSimplex.ofIsos F (fun i ↦ J ≫ (N i).1)
        (fun i ↦ δ ≪≫ isoWhiskerLeft J.functor (N i).2) =
      (ModelSimplex.ofIsos G (fun i ↦ (N i).1) (fun i ↦ (N i).2)).precomp J := by
  rw [ModelSimplex.ofIsos_change_reference]
  exact (ModelSimplex.ofIsos_precomp _ _ _ _).symm

variable (X : Scheme.{u})

/-- The common carrier keeps the actual base-unit/projection source and every node anchor. -/
abbrev Carrier := |nerve (Codiscrete (CommonReferenceNerve.Node (source X)))|

/-- The entire initial face is the original thirty-one-node input surface in that carrier. -/
def inputFace : C(unitInterval × unitInterval, Carrier X) :=
  (CommonReferenceNerve.parameter (source X) (nodes X)).comp BassH0Diagram.parameter

/-- Every original input level and both native clocks survive the characteristic-map lift. -/
theorem inputFace_native (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen X)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (source X) (inputFace X) n ((s, t), x) =
      (inputComparisonHomotopy (𝟙 X)).level n
        (s, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (projection.app X))
          (boundedFlatPerfectPrespectrumMap (projection.app X)) n (t, x)) := by
  refine (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex (source X)
    (inputFace X) (nodes X) (s, t) (BassH0Diagram.parameter (s, t)) rfl n x).trans ?_
  rw [CommonReferenceNerve.prespectrumFamily_eq]
  exact InputIdentityNodes.cylinder_native X n s t x

variable (k : laurent ⟶ polynomial)
  (hk : ∀ Z, k.app Z ≫ projection.app Z = laurentProjection.app Z)

/-- The entire actual precomposed unit-square simplex retains its complete source anchor. -/
theorem chart_family :
    ModelSimplex.ofIsos (source X) (fun i ↦ (chartSideNodes X k hk i).1)
      (fun i ↦ (chartSideNodes X k hk i).2) =
        (OriginalUnitSquareSimplex.simplex (k.app X)).precomp
          (OriginalUnitSquareSimplex.sourceMap (projection.app X)) :=
  pre_family (source X) (OriginalUnitSquareSimplex.sourceMap (projection.app X))
    (OriginalUnitSquareSimplex.sourceMap (k.app X))
    (chartProjectionIso X k hk ≪≫
      BinaryNormalizationSimplex.total (k.app X) (projection.app X))
    (fun i ↦ ⟨OriginalUnitSquareSimplex.vertices (k.app X) i,
      OriginalUnitSquareSimplex.references (k.app X) i⟩)

/-- Each whole chart face uses its original eight nodes and the unchanged unit-square clock. -/
def chartFace : C(unitInterval × unitInterval, Carrier X) :=
  (CommonReferenceNerve.parameter (source X) (chartSideNodes X k hk)).comp
    OriginalUnitSquareSimplex.squareParameter

/-- The complete chart carrier evaluates to the original geometric unit square. -/
theorem chartFace_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen X)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (source X) (chartFace X k hk) n ((r, s), x) =
      (boundedFlatPerfectPrespectrumUnitSquare (k.app X)).level n
        (r, (s, (boundedFlatPerfectPrespectrumMap (projection.app X)).map n x)) := by
  refine (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex (source X)
    (chartFace X k hk) (chartSideNodes X k hk) (r, s)
    (OriginalUnitSquareSimplex.squareParameter (r, s)) rfl n x).trans ?_
  rw [CommonReferenceNerve.prespectrumFamily_eq, chart_family]
  exact (prespectrumSimplexFamily_precomp (OriginalUnitSquareSimplex.simplex (k.app X))
    (OriginalUnitSquareSimplex.sourceMap (projection.app X)) n
    (OriginalUnitSquareSimplex.squareParameter (r, s)) x).trans
      (OriginalUnitSquareSimplex.square_native (k.app X) n r s _)

/-- The positive face is the specified original identity chart, with its actual map-id transport. -/
theorem plusFace_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen X)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (source X)
      (chartFace X plus plus_projection) n ((r, s), x) =
        (InputIdentity.plusSquare X).level n
          (r, (s, (boundedFlatPerfectPrespectrumMap (projection.app X)).map n x)) :=
  chartFace_native X plus plus_projection n r s x

/-- The inverse face retains its distinct unit square and the same original polynomial premap. -/
theorem minusFace_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen X)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (source X)
      (chartFace X minus minus_projection) n ((r, s), x) =
        (InputIdentity.minusSquare X).level n
          (r, (s, (boundedFlatPerfectPrespectrumMap (projection.app X)).map n x)) :=
  chartFace_native X minus minus_projection n r s x

end Quillen.PerfectComplexes.GlobalRawBass.InputIdentityCarrierCharts
