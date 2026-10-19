/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputTripleNodes

/-!
# Full postcomposed evaluation nodes in the original raw triple

The three normalization nodes of the original evaluation chart, after actual raw pullback,
are the same complete dependent nodes as the left binary face of the original split triple.
Their reference equalities use the original global evaluation composition pasting.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.GlobalBassEvaluation.InputTripleNodes
open GlobalSectionChangeIndex
variable {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)

private theorem post_total_anchor :
    (evaluationCompositionFirstIso f (g ≫ h)).hom ≫
      (isoWhiskerRight (evaluationComparisonIso (g ≫ h)) (evaluationRawMap f).functor).hom =
    (evaluationComparisonIso (f ≫ g ≫ h)).hom ≫
      (isoWhiskerLeft (evaluationModel (op T)).functor
        (NormalizedTripleSimplex.leftFirst f g h)).hom := by
  apply NatTrans.ext
  funext x
  have e := NatTrans.congr_app (evaluationComposition_pasting f (g ≫ h)).symm x
  simpa only [evaluationCompositionSecondIso, evaluationCompositionTargetIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.associator_inv_app,
    Category.comp_id, evaluationRawCompIso, NormalizedTripleSimplex.leftFirst] using e

/-- The total raw node agrees with its original postcomposed evaluation node, including anchor. -/
theorem post_total_node : postNode f g h 1 = rawNode f g h 2 := by
  apply ModelSimplex.reference_node_eq (by rfl)
  simp only [eqToHom_refl, Category.comp_id]
  exact post_total_anchor f g h

/-- The actual geometric intermediate retains its entire original postcomposed reference. -/
theorem post_intermediate_node : postNode f g h 2 = rawNode f g h 3 := by
  apply ModelSimplex.reference_node_eq (by rfl)
  simp only [eqToHom_refl, Category.comp_id]
  change (evaluationCompositionFirstIso f (g ≫ h)).hom ≫
    (isoWhiskerRight (evaluationComparisonIso (g ≫ h) ≪≫ InputSimplex.geometricIso g h)
      (evaluationRawMap f).functor).hom =
    (evaluationComparisonIso (f ≫ g ≫ h)).hom ≫
      (isoWhiskerLeft (evaluationModel (op T)).functor
        (NormalizedTripleSimplex.leftFirst f g h ≪≫
          SplitTripleSimplex.leftSecondGeometric f g h)).hom
  simp only [isoWhiskerRight_trans, isoWhiskerLeft_trans, Iso.trans_hom, ← Category.assoc]
  rw [post_total_anchor]
  rfl

/-- The fully split target retains both original geometric and evaluation reference paths. -/
theorem post_target_node : postNode f g h 4 = rawNode f g h 7 := by
  apply ModelSimplex.reference_node_eq (by rfl)
  simp only [eqToHom_refl, Category.comp_id]
  change (evaluationCompositionFirstIso f (g ≫ h)).hom ≫
    (isoWhiskerRight (evaluationComparisonIso (g ≫ h) ≪≫ evaluationCompositionTargetIso g h)
      (evaluationRawMap f).functor).hom =
    (evaluationComparisonIso (f ≫ g ≫ h)).hom ≫
      (isoWhiskerLeft (evaluationModel (op T)).functor
        (NormalizedTripleSimplex.leftFirst f g h ≪≫
          NormalizedTripleSimplex.leftSecond f g h)).hom
  simp only [isoWhiskerRight_trans, isoWhiskerLeft_trans, Iso.trans_hom, ← Category.assoc]
  rw [post_total_anchor]
  apply NatTrans.ext
  funext x
  simp only [evaluationCompositionTargetIso, NormalizedTripleSimplex.leftSecond,
    evaluationRawCompIso, Iso.trans_hom, Iso.symm_hom, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id]
  rfl

end Quillen.PerfectComplexes.GlobalBassEvaluation.InputTripleNodes
