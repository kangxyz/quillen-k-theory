/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassH0ProjectionColumns

/-! Full dependent comparison of the original positive H0 and bottom source columns. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.PolynomialBaseChange Quillen.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS
universe u v
namespace Quillen.PerfectComplexes.BassH0Merge
open BassReferenceMerge

section Functors
variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
theorem composition_pair_refl {F₀ F₁ : C ⥤ D} (e : F₀ ≅ F₁) (G : D ⥤ E) :
    (Functor.uncurry.obj (whiskeringLeft C D E)).mapIso (e.prod (Iso.refl G)) =
      isoWhiskerRight e G := by
  rw [composition_pair_iso, isoWhiskerLeft_refl, Iso.trans_refl]
end Functors

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

theorem bottom_anchor_iso : BassBottomCommonFamily.referenceIso P u v =
    eqToIso (bottom_reference_eq P u v) ≪≫ BinaryNormalizationSimplex.total
      (laurentComposite P u v) (laurentPlus P a ≫ polynomialProjection P a) := by
  change smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
      (BassBottomCommonFamily.bottom_total P u v).symm) ≪≫
      boundedFlatNormalizedPullbackCompIso (laurentComposite P u v)
        (laurentPlus P a ≫ polynomialProjection P a)) = _
  rw [smallIso_trans, smallIso_eqToIso]
  rfl

theorem projection_plus_nodes (i : Fin 3) :
    BassProjectionPath.nodes P a (Fin.castAdd 2 i) =
      binaryNodes (laurentPlus P a) (polynomialProjection P a) i := by
  fin_cases i <;> rfl

/-- The whole original positive bottom column keeps every actual binary reference isomorphism. -/
theorem bottom_plus_column (i : Fin 3) :
    BassReferenceMerge.nodes P u v (BassReferenceMerge.bottomFace.toOrderHom
      (Quillen.SimplexGrid.index 4 2 (Fin.castAdd 2 i, 0))) =
      binaryColumnNode (BassOverlap.commonReference P u v) (laurentComposite P u v)
        (laurentPlus P a) (polynomialProjection P a) (bottom_reference_eq P u v) i := by
  rw [BassReferenceMerge.bottom_nodes]
  change BassBottomCommonFamily.nodes P u v
    (Fin.natAdd 36 (Quillen.SimplexGrid.index 4 2 (Fin.castAdd 2 i, 0))) = _
  unfold BassBottomCommonFamily.nodes
  rw [Fin.addCases_right]
  unfold BassBottomCommonFamily.bottomNodes CommonReferenceProduct.vertices
    CommonReferenceProduct.references
  rw [Quillen.SimplexGrid.decode_index]
  dsimp only
  rw [projection_plus_nodes P (a := a) i]
  have hf : ((binaryNodes (laurentPlus P a) (polynomialProjection P a) i).1 ≫
      BassLaurentBottomFace.vertices P u v 0).functor =
    (binaryColumnNode (BassOverlap.commonReference P u v) (laurentComposite P u v)
      (laurentPlus P a) (polynomialProjection P a) (bottom_reference_eq P u v) i).1.functor := rfl
  apply Sigma.ext (Model.Hom.ext hf)
  apply heq_of_eq
  change BassBottomCommonFamily.referenceIso P u v ≪≫
    (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
      ((binaryNodes (laurentPlus P a) (polynomialProjection P a) i).2.prod
        (Iso.refl (BassLaurentBottomFace.source P u v).functor)) =
      (eqToIso (bottom_reference_eq P u v) ≪≫ BinaryNormalizationSimplex.total
        (laurentComposite P u v) (laurentPlus P a ≫ polynomialProjection P a)) ≪≫
          isoWhiskerRight (binaryNodes (laurentPlus P a) (polynomialProjection P a) i).2
            (normalizedMap (laurentComposite P u v)).functor
  rw [composition_pair_refl, bottom_anchor_iso]
  rfl

/-- All three positive source-edge nodes agree, including the original raw intermediate. -/
theorem positive_source_nodes (i : Fin 3) :
    nodes P u v (BassH0Diagram.plusFace.toOrderHom (rectangleLeftIndex i)) =
      BassReferenceMerge.nodes P u v (BassReferenceMerge.bottomFace.toOrderHom
        (Quillen.SimplexGrid.index 4 2 (Fin.castAdd 2 i, 0))) := by
  rw [plus_source_column, bottom_plus_column]
  exact binaryColumnNode_congr _ _ _ _ _ (laurent_composite P u v) _ i

/-- Full shared raw node (H0 index 3, old merged index 18). -/
theorem shared_positive_raw_node : nodes P u v 3 = BassReferenceMerge.nodes P u v 18 :=
  positive_source_nodes P u v 1

/-- Full shared normalized endpoint (H0 index 11, old merged index 21). -/
theorem shared_positive_target_node : nodes P u v 11 = BassReferenceMerge.nodes P u v 21 :=
  positive_source_nodes P u v 2

end Quillen.PerfectComplexes.BassH0Merge
