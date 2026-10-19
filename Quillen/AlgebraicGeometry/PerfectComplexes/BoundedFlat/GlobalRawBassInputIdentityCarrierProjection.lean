/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputIdentityProjection
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.OriginalUnitSquareSupport

/-!
# The terminal carrier face of the original global raw identity boundary

The genuine projection path is reanchored to the same complete source reference as the input
and chart faces. The terminal face keeps every original cylinder time and is constant only in
the comparison coordinate. Its two chart joins use complete node equalities.
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
namespace Quillen.PerfectComplexes.GlobalRawBass.InputIdentityCarrierProjection
open BassH0Merge InputIdentityCarrierCharts OriginalUnitSquareSimplex
open CoefficientBassUnitHZeroNodes

private theorem anchored_family {V W : Model.{u}} {F G : V ⟶ W} {k : ℕ}
    (ρ : F.functor ≅ G.functor) (N : Fin (k + 1) → CommonReferenceNerve.Node G) :
    ModelSimplex.ofIsos F (fun i ↦ (anchorNode ρ (N i)).1)
        (fun i ↦ (anchorNode ρ (N i)).2) =
      ModelSimplex.ofIsos G (fun i ↦ (N i).1) (fun i ↦ (N i).2) :=
  ModelSimplex.ofIsos_change_reference ρ _ _

private theorem rectangle_terminal {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B)
    (F : modelOf (boundedFlatPerfectWaldhausen A) ⟶
      modelOf (boundedFlatPerfectWaldhausen C))
    (δ : F.functor ≅ (BinaryNormalizationSimplex.sourceMap q p).functor) :
    rectangleSideNodes p q F δ 7 =
      ⟨BinaryNormalizationSimplex.targetMap q p, δ ≪≫ BinaryNormalizationSimplex.total q p⟩ := by
  have h : rightFirst q ≪≫ rightSecond q = Iso.refl _ :=
    Iso.ext (CoefficientBassUnitBoundaryNodes.right_route_identity q)
  change preReferenceNode F (sourceMap p) (δ ≪≫ BinaryNormalizationSimplex.total q p)
    ⟨sourceMap q, rightFirst q ≪≫ rightSecond q⟩ = _
  rw [h]
  exact preReferenceNode_source _ _ _

private theorem parameter_single_eq {V W : Model.{u}} (F : V ⟶ W) {p q : ℕ}
    (N : Fin (p + 1) → CommonReferenceNerve.Node F)
    (M : Fin (q + 1) → CommonReferenceNerve.Node F)
    (i : Fin (p + 1)) (j : Fin (q + 1)) (h : N i = M j) :
    CommonReferenceNerve.parameter F N (StdSimplex.single i) =
      CommonReferenceNerve.parameter F M (StdSimplex.single j) := by
  let α : ⦋0⦌ ⟶ ⦋p⦌ := SimplexCategory.Hom.mk ⟨fun _ ↦ i, fun _ _ _ ↦ le_rfl⟩
  let β : ⦋0⦌ ⟶ ⦋q⦌ := SimplexCategory.Hom.mk ⟨fun _ ↦ j, fun _ _ _ ↦ le_rfl⟩
  have e := CommonReferenceNerve.parameter_eq_of_face_nodes F M N β α
    (fun _ ↦ h) (StdSimplex.single 0)
  rw [StdSimplex.map_single, StdSimplex.map_single] at e
  exact e

variable (X : Scheme.{u})

/-- All five actual projection nodes retain the complete base-unit reference. -/
def nodes (i : Fin 5) : InputIdentityNodes.Node X :=
  anchorNode (InputIdentityNodes.sourceToProjection X) (InputIdentityProjection.nodes X i)

/-- The entire original projection simplex is preserved by this reference change. -/
theorem projection_family :
    ModelSimplex.ofIsos (InputIdentityNodes.source X) (fun i ↦ (nodes X i).1)
      (fun i ↦ (nodes X i).2) = InputIdentityProjection.simplex X :=
  anchored_family (InputIdentityNodes.sourceToProjection X) (InputIdentityProjection.nodes X)

/-- The terminal face retains the original full cylinder path and ignores only comparison time. -/
def face : C(unitInterval × unitInterval, Carrier X) :=
  ((CommonReferenceNerve.parameter (InputIdentityNodes.source X) (nodes X)).comp
    InputIdentityProjection.parameter.toContinuousMap).comp ContinuousMap.snd

/-- Its whole compact evaluation is the literal unpaused identity track on the original cylinder. -/
theorem face_native (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen X)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputIdentityNodes.source X) (face X)
        n ((s, t), x) =
      (coneSquareIdentityTrack (comparison X)).level n
        (s, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (projection.app X))
          (boundedFlatPerfectPrespectrumMap (projection.app X)) n (t, x)) := by
  refine (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex (InputIdentityNodes.source X)
    (face X) (nodes X) (s, t) (InputIdentityProjection.parameter t) rfl n x).trans ?_
  rw [CommonReferenceNerve.prespectrumFamily_eq, projection_family]
  exact InputIdentityProjection.native X n t x

/-- The terminal positive node keeps the full original chart anchor, including unit cancellation. -/
theorem plus_node : nodes X 2 = InputIdentityNodes.chartSideNodes X plus plus_projection 7 := by
  have h : InputIdentityNodes.chartProjectionIso X plus plus_projection =
      InputIdentityNodes.sourceToProjection X := Iso.trans_refl _
  have e := rectangle_terminal (projection.app X) (plus.app X) (InputIdentityNodes.source X)
    (InputIdentityNodes.chartProjectionIso X plus plus_projection)
  rw [h] at e
  exact e.symm

/-- The inverse terminal anchor retains the original projection transport before cancellation. -/
theorem minus_node : nodes X 4 =
    InputIdentityNodes.chartSideNodes X minus minus_projection 7 := by
  have e := rectangle_terminal (projection.app X) (minus.app X) (InputIdentityNodes.source X)
    (InputIdentityNodes.chartProjectionIso X minus minus_projection)
  refine Eq.trans ?_ e.symm
  change (⟨_, InputIdentityNodes.sourceToProjection X ≪≫
    (InputIdentityProjection.sourceIso X ≪≫ BinaryNormalizationSimplex.total
      (minus.app X) (projection.app X))⟩ : InputIdentityNodes.Node X) =
    ⟨_, (InputIdentityNodes.sourceToProjection X ≪≫ InputIdentityProjection.sourceIso X) ≪≫
      BinaryNormalizationSimplex.total (minus.app X) (projection.app X)⟩
  exact congrArg (fun η ↦ (⟨BinaryNormalizationSimplex.targetMap
    (minus.app X) (projection.app X), η⟩ : InputIdentityNodes.Node X))
      (Iso.trans_assoc _ _ _).symm

/-- The entire terminal-positive seam agrees as a continuous path in the actual carrier. -/
theorem plus_seam :
    (face X).comp ⟨fun s : unitInterval ↦ (s, 0), by fun_prop⟩ =
      (chartFace X plus plus_projection).comp
        ⟨fun s : unitInterval ↦ (1, s), by fun_prop⟩ := by
  apply ContinuousMap.ext
  intro s
  change CommonReferenceNerve.parameter (InputIdentityNodes.source X) (nodes X)
      (InputIdentityProjection.parameter 0) =
    CommonReferenceNerve.parameter (InputIdentityNodes.source X)
      (InputIdentityNodes.chartSideNodes X plus plus_projection)
      (OriginalUnitSquareSimplex.squareParameter (1, s))
  rw [Path.source, OriginalUnitSquareSupport.square_top_path]
  exact parameter_single_eq _ _ _ _ _ (plus_node X)

/-- The inverse terminal seam keeps its distinct original chart and unchanged comparison clock. -/
theorem minus_seam :
    (face X).comp ⟨fun s : unitInterval ↦ (s, 1), by fun_prop⟩ =
      (chartFace X minus minus_projection).comp
        ⟨fun s : unitInterval ↦ (1, s), by fun_prop⟩ := by
  apply ContinuousMap.ext
  intro s
  change CommonReferenceNerve.parameter (InputIdentityNodes.source X) (nodes X)
      (InputIdentityProjection.parameter 1) =
    CommonReferenceNerve.parameter (InputIdentityNodes.source X)
      (InputIdentityNodes.chartSideNodes X minus minus_projection)
      (OriginalUnitSquareSimplex.squareParameter (1, s))
  rw [Path.target, OriginalUnitSquareSupport.square_top_path]
  exact parameter_single_eq _ _ _ _ _ (minus_node X)

end Quillen.PerfectComplexes.GlobalRawBass.InputIdentityCarrierProjection
