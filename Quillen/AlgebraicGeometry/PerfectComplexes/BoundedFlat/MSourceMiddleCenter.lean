/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MReferenceRows
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MReassociationNative

/-! The actual central full node on the M-source/H0-target boundary. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.PolynomialBaseChange AlgebraicGeometry.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassMOuterJoin
open BassReferenceMerge BassH0Merge BassMComponents BassMReferences
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The original H0 target reference is induced by its actual geometric coefficient composite. -/
theorem h0TargetReference : (BassOverlap.commonReference P u v).functor =
    (BinaryNormalizationSimplex.sourceMap (laurentProjection P c)
      (coefficientMap P (u ≫ v))).functor :=
  (reference_eq P u v).trans (congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
    (congrArg boundedFlatNormalizedPullback (BassH1H0Boundary.laurent_naturality P (u ≫ v))))

/-- The actual common middle source uses the original positive projection factorization. -/
theorem middleSourceReference : (BassOverlap.commonReference P u v).functor =
    (BinaryNormalizationSimplex.sourceMap (laurentPlus P c ≫ polynomialProjection P c)
      (coefficientMap P v ≫ coefficientMap P u)).functor :=
  congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
    (congrArg boundedFlatNormalizedPullback (middle_total P u v).symm)

/-- H0's full central target node retains the original anchored binary normalization. -/
theorem h0_target_center_canonical : BassH0Merge.nodes P u v 26 =
    binaryTargetNode (BassOverlap.commonReference P u v)
      (laurentProjection P c) (coefficientMap P (u ≫ v)) (h0TargetReference P u v) := by
  have hn := congrArg (anchorNode (F₀ := BassOverlap.commonReference P u v)
    (F₁ := BassH0Diagram.reference P (u ≫ v)) (eqToIso (reference_eq P u v)))
      (BassH1H0Boundary.target_normal P (u ≫ v))
  exact hn.trans (anchor_binary_target_node (BassOverlap.commonReference P u v)
    (BassH0Diagram.reference P (u ≫ v)) (laurentProjection P c) (coefficientMap P (u ≫ v))
    (reference_eq P u v) (congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
      (congrArg boundedFlatNormalizedPullback
        (BassH1H0Boundary.laurent_naturality P (u ≫ v)))))

/-- The product source node is the same full binary target in its own factorization. -/
theorem middle_source_center_canonical : middleNodes P u v 0 =
    binaryTargetNode (BassOverlap.commonReference P u v)
      (laurentPlus P c ≫ polynomialProjection P c) (coefficientMap P v ≫ coefficientMap P u)
      (middleSourceReference P u v) := by
  change middleNodes P u v (Quillen.SimplexGrid.index 2 4 (0, 0)) = _
  unfold middleNodes BassH1Join.reanchoredProductNode CommonReferenceProduct.vertices
    CommonReferenceProduct.references
  rw [Quillen.SimplexGrid.decode_index]
  dsimp only
  have hf : ((coefficientNodes P u v 0).1 ≫ (BassProjectionPath.nodes P c 0).1).functor =
      (BinaryNormalizationSimplex.targetMap (laurentPlus P c ≫ polynomialProjection P c)
        (coefficientMap P v ≫ coefficientMap P u)).functor := rfl
  apply Sigma.ext (Model.Hom.ext hf)
  apply heq_of_eq
  change middleIso P u v ≪≫
    (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
      ((Iso.refl (coefficientSource P u v).functor).prod
        (Iso.refl (BassProjectionPath.source P c).functor)) =
      eqToIso (middleSourceReference P u v) ≪≫ BinaryNormalizationSimplex.total
        (laurentPlus P c ≫ polynomialProjection P c) (coefficientMap P v ≫ coefficientMap P u)
  rw [composition_pair_iso, isoWhiskerRight_refl, isoWhiskerLeft_refl, Iso.refl_trans]
  refine (Iso.trans_refl (middleIso P u v)).trans ?_
  change smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
    (middle_total P u v).symm) ≪≫ boundedFlatNormalizedPullbackCompIso
      (laurentPlus P c ≫ polynomialProjection P c) (coefficientMap P v ≫ coefficientMap P u)) = _
  rw [smallIso_trans, smallIso_eqToIso]
  rfl

/-- The M source-middle centre is the actual H0 target node, with its full reference. -/
theorem source_middle_center : middleNodes P u v 0 = BassH0Merge.nodes P u v 26 := by
  rw [middle_source_center_canonical, h0_target_center_canonical]
  exact binaryTargetNode_congr _ (laurentPlus_projection P c)
    (coefficientMap_comp P u v).symm _ _

end Quillen.PerfectComplexes.BassMOuterJoin
