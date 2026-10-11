/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.TwoOpenSectionLifting
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.TautologicalQuotient
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.TautologicalCohomology
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.StructureSheafCohomology

/-! # Actual cohomology of the tautological quotient

The original quotient projection induces an isomorphism on global additive sections, by correcting
its chart lifts with the proved tautological-line signed difference. The literal quotient map then
identifies these sections with two copies of the base ring. Surjectivity of its original signed
difference and the higher two-affine-cover theorem give vanishing in every positive derived degree.
All statements allow arbitrary commutative rings, including the zero ring.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.Scheme.ProjectiveLine
open Quillen.SchemeSheaf Quillen.SchemeSheaf.TwoOpen
variable (R : CommRingCat.{u})

/-- The positive signed row supplies an explicit section of the restricted quotient map. -/
def tautologicalQuotientPlusSplit :
    SplitEpi ((Scheme.Modules.restrictFunctor (plusChart R)).map (tautologicalQuotientMap R)) where
  section_ := (tautologicalQuotientPlusIso R).hom ≫ graphSection ≫
    (unitSquareRestrictionIso (plusChart R)).inv
  id := by
    apply (cancel_mono (tautologicalQuotientPlusIso R).hom).mp
    simp only [Category.assoc, tautologicalQuotientMap_plus, firstRow,
      Iso.inv_hom_id_assoc, graphSection_row, Category.comp_id, Category.id_comp]

/-- The negative signed row supplies an explicit section of the restricted quotient map. -/
def tautologicalQuotientMinusSplit :
    SplitEpi ((Scheme.Modules.restrictFunctor (minusChart R)).map (tautologicalQuotientMap R)) where
  section_ := (tautologicalQuotientMinusIso R).hom ≫ cographSection ≫
    (unitSquareRestrictionIso (minusChart R)).inv
  id := by
    apply (cancel_mono (tautologicalQuotientMinusIso R).hom).mp
    simp only [Category.assoc, tautologicalQuotientMap_minus, secondRow,
      Iso.inv_hom_id_assoc, cographSection_row, Category.comp_id, Category.id_comp]

/-- The original quotient map is surjective on positive-chart sections. -/
lemma tautologicalQuotientMap_plusSections_surjective :
    Function.Surjective
      (Scheme.Modules.Hom.app (tautologicalQuotientMap R) (plusChart R).opensRange).hom := by
  let := IsSplitEpi.mk' (tautologicalQuotientPlusSplit R)
  exact (plusChart R).image_top_eq_opensRange ▸
    section_surjective_of_restriction_split (plusChart R) (tautologicalQuotientMap R) ⊤

/-- The original quotient map is surjective on negative-chart sections. -/
lemma tautologicalQuotientMap_minusSections_surjective :
    Function.Surjective
      (Scheme.Modules.Hom.app (tautologicalQuotientMap R) (minusChart R).opensRange).hom := by
  let := IsSplitEpi.mk' (tautologicalQuotientMinusSplit R)
  exact (minusChart R).image_top_eq_opensRange ▸
    section_surjective_of_restriction_split (minusChart R) (tautologicalQuotientMap R) ⊤

/-- The original quotient map is surjective on actual overlap sections. -/
lemma tautologicalQuotientMap_overlapSections_surjective :
    Function.Surjective (Scheme.Modules.Hom.app (tautologicalQuotientMap R)
      ((plusChart R).opensRange ⊓ (minusChart R).opensRange)).hom := by
  let := IsSplitEpi.mk' (tautologicalQuotientPlusSplit R)
  exact (plusChart R).image_preimage_eq_opensRange_inf (minusChart R).opensRange ▸
    section_surjective_of_restriction_split (plusChart R) (tautologicalQuotientMap R)
      ((plusChart R) ⁻¹ᵁ (minusChart R).opensRange)

/-- The checked tautological difference corrects local lifts to an original global lift. -/
lemma tautologicalQuotientMap_globalSections_surjective :
    Function.Surjective (Scheme.Modules.Hom.app (tautologicalQuotientMap R) ⊤).hom :=
  globalSections_surjective_of_difference_surjective (tautologicalSequence_shortExact R)
    (plusChart R).opensRange (minusChart R).opensRange (chart_ranges_cover R)
    (tautologicalQuotientMap_plusSections_surjective R)
    (tautologicalQuotientMap_minusSections_surjective R)
    (tautological_difference_surjective R)

/-- The original quotient projection induces an isomorphism on global additive sections. -/
instance tautologicalQuotientMap_globalSections_isIso :
    IsIso (Scheme.Modules.Hom.app (tautologicalQuotientMap R) ⊤) := by
  have hm := (sections_exact (tautologicalSequence_shortExact R) ⊤).mono_g
    ((isZero_globalSections_tautologicalLine R).eq_of_src _ _)
  let : Mono (Scheme.Modules.Hom.app (tautologicalQuotientMap R) ⊤) := hm
  have he : Epi (Scheme.Modules.Hom.app (tautologicalQuotientMap R) ⊤) :=
    (AddCommGrpCat.epi_iff_surjective _).mpr (tautologicalQuotientMap_globalSections_surjective R)
  exact isIso_of_mono_of_epi _

/-- The quotient has surjective original signed difference, inherited from the unit square. -/
lemma tautologicalQuotient_difference_surjective :
    Function.Surjective (difference (tautologicalQuotientLine R)
      (plusChart R).opensRange (minusChart R).opensRange) :=
  difference_surjective_of_section_surjective (tautologicalQuotientMap R) _ _
    (tautologicalQuotientMap_overlapSections_surjective R)
    (difference_surjective_prod _ _ _ _ (structureSheaf_difference_surjective R)
      (structureSheaf_difference_surjective R))

/-- All positive actual derived global sections of the quotient vanish over any base ring. -/
lemma isZero_rightDerived_tautologicalQuotientLine_succ (n : ℕ) :
    IsZero (((sectionsFunctor (twoChartLine R) ⊤).rightDerived (n + 1)).obj
      (tautologicalQuotientLine R)) := by
  cases n with
  | zero =>
    exact twoAffine_isZero_rightDerived_one_of_difference_surjective
      (tautologicalQuotientLine R) (plusChart R) (minusChart R) (chart_ranges_cover R)
      (tautologicalQuotient_difference_surjective R)
  | succ n => exact isZero_rightDerived_globalSections_add_two R (tautologicalQuotientLine R) n


/-- The two original constant coordinates identify global unit-square sections with two base
copies. -/
def unitSquareGlobalSectionsIso : AddCommGrpCat.of (R × R) ≅
    Γ(((SheafOfModules.unit (twoChartLine R).ringCatSheaf : (twoChartLine R).Modules) ⨯
      SheafOfModules.unit (twoChartLine R).ringCatSheaf), ⊤) := by
  let F := sectionsFunctor (twoChartLine R) ⊤
  let O : (twoChartLine R).Modules := SheafOfModules.unit (twoChartLine R).ringCatSheaf
  let e : AddCommGrpCat.of R ≅ F.obj O :=
    (globalSectionsIso R).commRingCatIsoToRingEquiv.toAddEquiv.toAddCommGrpIso
  let : PreservesBinaryBiproduct O O F :=
    preservesBinaryBiproduct_of_preservesBinaryProduct F
  exact (AddCommGrpCat.biprodIsoProd (.of R) (.of R)).symm ≪≫
    biprod.mapIso e e ≪≫ (F.mapBiprod O O).symm ≪≫ F.mapIso (biprod.isoProd O O)

/-- The original quotient projection identifies its global additive sections with two base
copies. -/
def tautologicalQuotientGlobalSectionsIso : AddCommGrpCat.of (R × R) ≅
    Γ(tautologicalQuotientLine R, ⊤) :=
  unitSquareGlobalSectionsIso R ≪≫ asIso (Scheme.Modules.Hom.app (tautologicalQuotientMap R) ⊤)

/-- The global-section identification retains the literal original quotient projection. -/
lemma tautologicalQuotientGlobalSectionsIso_hom :
    (tautologicalQuotientGlobalSectionsIso R).hom =
      (unitSquareGlobalSectionsIso R).hom ≫
        Scheme.Modules.Hom.app (tautologicalQuotientMap R) ⊤ := rfl

end Quillen.Scheme.ProjectiveLine
