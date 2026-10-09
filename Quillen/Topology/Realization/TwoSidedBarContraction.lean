import Quillen.Topology.Realization.TwoSidedBarColumn
import Quillen.Topology.Realization.TwoSidedBarDrop

/-! # The evaluation augmentation is a genuine equivalence

Each transposed row is the nerve of an elementary resolution category.
Its actual terminal section and augmentation-arrow transformation contract
it onto the discrete set of original diagonal simplices.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite
open scoped Simplicial Topology
universe u

namespace Quillen.TwoSidedBar
open TheoremA

/-- The nerve of a discrete category is the actual constant simplicial set. -/
def discreteNerveIso (A : Type u) :
    nerve (Discrete A) ≅ (Functor.const SimplexCategoryᵒᵖ).obj A :=
  NatIso.ofComponents (fun p ↦ Equiv.toIso {
    toFun F := (F.obj 0).as
    invFun a := (Functor.const (Fin (p.unop.len + 1))).obj (Discrete.mk a)
    left_inv F := by
      refine CategoryTheory.Functor.ext (fun i ↦ Discrete.ext (Discrete.eq_of_hom (F.map (homOfLE (Fin.zero_le i))))) ?_
      intro i j f
      apply Subsingleton.elim
    right_inv _ := rfl }) (by
    intro p q α
    ext F : 3
    exact (Discrete.eq_of_hom (F.map (homOfLE (Fin.zero_le (α.unop.toOrderHom 0))))).symm)

variable (H : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (q : SimplexCategoryᵒᵖ)

/-- The original evaluation functor is a classifying-space homotopy equivalence. -/
def resolutionEvaluationHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (Resolution H q))
      (ClassifyingSpace (Discrete ((H.obj q).obj q))) where
  toFun := (classifyingSpaceMap (Resolution.evaluate H q)).hom
  invFun := (classifyingSpaceMap (Resolution.sectionFunctor H q)).hom
  left_inv := by
    have h := classifyingSpaceNaturalTransformationHomotopy (Resolution.contraction H q)
    exact ⟨by simpa only [classifyingSpaceMap_id, classifyingSpaceMap_comp, TopCat.hom_id,
      TopCat.hom_comp] using h.symm⟩
  right_inv := by
    have h := classifyingSpaceNaturalTransformationHomotopy (Resolution.sectionEvaluationIso H q).hom
    exact ⟨by simpa only [classifyingSpaceMap_id, classifyingSpaceMap_comp, TopCat.hom_id,
      TopCat.hom_comp] using h⟩

/-- In the actual column coordinates evaluation is precisely the discrete
augmentation functor, including every initial/final transport. -/
theorem columnIso_evaluation :
    (columnIso H q).hom ≫ ((flipFunctor _ _ _).map (evaluation H)).app q =
      nerveMap (Resolution.evaluate H q) ≫ (discreteNerveIso ((H.obj q).obj q)).hom := by
  apply NatTrans.ext
  funext p
  apply ConcreteCategory.hom_ext
  intro F
  change (H.map (indexProjection.map ((F ⋙ Resolution.forget H q).map
      (homOfLE (Fin.zero_le (Fin.last p.unop.len)))) ≫ (F.obj (Fin.last p.unop.len)).arrow)).app q
        (F.obj 0).value = (H.map (F.obj 0).arrow).app q (F.obj 0).value
  exact congrArg (fun α ↦ (H.map α).app q (F.obj 0).value)
    (F.map (homOfLE (Fin.zero_le (Fin.last p.unop.len)))).arrow

/-- Every actual transposed evaluation row is a realization equivalence. -/
theorem evaluationColumn_isRealizationEquivalence :
    IsRealizationEquivalence (((flipFunctor _ _ _).map (evaluation H)).app q) := by
  apply IsRealizationEquivalence.of_iso_square _ (nerveMap (Resolution.evaluate H q))
    (columnIso H q).symm (discreteNerveIso ((H.obj q).obj q)).symm
  · change ((flipFunctor _ _ _).map (evaluation H)).app q ≫
        (discreteNerveIso ((H.obj q).obj q)).inv =
      (columnIso H q).inv ≫ nerveMap (Resolution.evaluate H q)
    have h := congrArg (fun f ↦ (columnIso H q).inv ≫ f ≫
        (discreteNerveIso ((H.obj q).obj q)).inv) (columnIso_evaluation H q)
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id] using h
  · exact ⟨resolutionEvaluationHomotopyEquiv H q, rfl⟩

end Quillen.TwoSidedBar
