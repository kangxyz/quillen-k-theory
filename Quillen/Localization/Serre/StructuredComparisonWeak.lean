import Quillen.Localization.Serre.NormalizedStructuredComma
import Quillen.Localization.Serre.LocalizationLESAdapter

/-! Transport from the genuine normalized structured identity comparison to
the already defined based localization comparison. The missing geometric
comparison remains an explicit input, not an axiom or a completed endpoint. -/
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
set_option backward.isDefEq.respectTransparency false
namespace Quillen.TheoremB
variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)

theorem structuredFiberComparison_identity_of_eq (c : C) (d : D) (h : F.obj c = d) :
    structuredFiberComparison F d
      (classifyingSpacePoint (StructuredArrow.mk (eqToHom h.symm))) =
      HomotopyFiber.basepoint (classifyingSpaceMap F).hom (classifyingSpacePoint d)
        (classifyingSpacePoint c)
        ((classifyingSpaceMap_point F c).trans (congrArg classifyingSpacePoint h)) := by
  subst d
  exact structuredFiberComparison_identity F c

theorem structuredFiberComparison_bijective_of_eq (c : C) (d : D) (h : F.obj c = d) (n : ℕ)
    (hb : Function.Bijective (homotopyGroupMap (N := Fin n)
      (structuredFiberComparison F (F.obj c)) (structuredFiberComparison_identity F c))) :
    Function.Bijective (homotopyGroupMap (N := Fin n) (structuredFiberComparison F d)
      (structuredFiberComparison_identity_of_eq F c d h)) := by
  subst d
  exact hb
end Quillen.TheoremB

namespace Quillen.SerreLocalization
attribute [local instance] Abelian.hasFiniteBiproducts quotientAbelian
variable {C : Type u} [Category.{u} C] [Abelian C]
  (P : ObjectProperty C) [P.IsSerreClass]

theorem quotientNormalized_obj_zero :
    (quotientNormalizedQ P).obj (abelianExactStructure C).qZero =
      (quotientExactStructure P).qZero := rebaseFunctor_obj_base _ _ _ _

theorem normalizedSerreToZeroStructuredComma_obj_zero :
    (normalizedSerreToZeroStructuredComma P).obj (Devissage.subcategoryExactStructure P).qZero =
      StructuredArrow.mk (eqToHom (quotientNormalized_obj_zero P).symm) := by
  have hi : (inclusionNormalizedQ P).obj (Devissage.subcategoryExactStructure P).qZero =
      (abelianExactStructure C).qZero :=
    rebaseFunctor_obj_base (Devissage.mapQ P)
      (Devissage.subcategoryExactStructure P).qZero (abelianExactStructure C).qZero
      ((abelianExactStructure C).qIsoOfIso (Devissage.exactInclusion P).toFunctor.mapZeroObject)
  refine StructuredArrow.obj_ext _ _ hi ?_
  apply (cancel_mono (eqToHom (quotientNormalized_obj_zero P))).1
  exact ((quotientExactStructure P).qHom_subsingleton_of_isZero _ _ (isZero_zero _)).elim _ _

theorem normalizedSerreToZeroStructuredComma_map_basepoint :
    classifyingSpaceMap (normalizedSerreToZeroStructuredComma P)
      (Devissage.subcategoryExactStructure P).kBasepoint =
      classifyingSpacePoint (StructuredArrow.mk (eqToHom (quotientNormalized_obj_zero P).symm)) :=
  (classifyingSpaceMap_point (normalizedSerreToZeroStructuredComma P)
    (Devissage.subcategoryExactStructure P).qZero).trans
      (congrArg classifyingSpacePoint (normalizedSerreToZeroStructuredComma_obj_zero P))

theorem normalizedStructuredFiberComparison_basepoint :
    normalizedStructuredFiberComparison P (Devissage.subcategoryExactStructure P).kBasepoint =
      normalizedFiberBasepoint P :=
  ((normalizedStructuredFiberComparisonHomotopy P).map_one_left _).symm.trans
    (normalizedStructuredFiberComparisonHomotopy_based P 1)

/-- The geometric structured identity comparison, when proved, transfers to
exactly the chosen based localization comparison in every degree, including π₀. -/
theorem basedLocalizationFiberComparison_bijective_of_structured (n : ℕ)
    (hb : Function.Bijective (homotopyGroupMap (N := Fin n)
      (TheoremB.structuredFiberComparison (quotientNormalizedQ P)
        ((quotientNormalizedQ P).obj (abelianExactStructure C).qZero))
      (TheoremB.structuredFiberComparison_identity (quotientNormalizedQ P)
        (abelianExactStructure C).qZero))) :
    Function.Bijective (homotopyGroupMap (N := Fin n) (basedLocalizationFiberComparison P)
      (basedLocalizationFiberComparison_basepoint P)) := by
  have h₁ := homotopyGroupMap_bijective_of_homotopyEquiv
    (normalizedZeroStructuredCommaClassifyingHomotopyEquiv P)
    (normalizedSerreToZeroStructuredComma_map_basepoint P) n
  have h₂ := TheoremB.structuredFiberComparison_bijective_of_eq
    (quotientNormalizedQ P) (abelianExactStructure C).qZero
    (quotientExactStructure P).qZero (quotientNormalized_obj_zero P) n hb
  have hcomp := homotopyGroupMap_bijective_comp
    (classifyingSpaceMap (normalizedSerreToZeroStructuredComma P)).hom
    (TheoremB.structuredFiberComparison (quotientNormalizedQ P) (quotientExactStructure P).qZero)
    (normalizedSerreToZeroStructuredComma_map_basepoint P)
    (TheoremB.structuredFiberComparison_identity_of_eq (quotientNormalizedQ P)
      (abelianExactStructure C).qZero (quotientExactStructure P).qZero
      (quotientNormalized_obj_zero P)) n h₁ h₂
  exact homotopyGroupMap_bijective_of_based_homotopy
    (normalizedStructuredFiberComparison_basepoint P)
    (basedLocalizationFiberComparison_basepoint P)
    (normalizedStructuredFiberComparisonHomotopy P).symm
    (fun t ↦ normalizedStructuredFiberComparisonHomotopy_based P (unitInterval.symm t)) n hcomp

end Quillen.SerreLocalization
