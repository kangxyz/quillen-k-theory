/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.UnitProperties
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.Cohomology
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.CechDifference
public import Aglib.AlgebraicGeometry.Cohomology.MayerVietoris.FirstCohomology
public import Aglib.AlgebraicGeometry.Modules.FinitePresentation.Basic
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Basic
/-!
# Structure-sheaf cohomology of the original projective line

The canonical section identifications of the polynomial charts and Laurent
intersection intertwine the literal signed restriction maps. Transporting the
Laurent splitting through this square proves surjectivity of the original
structure-sheaf section difference. The actual two-affine-cover cokernel
comparison then proves vanishing of first right-derived global sections.
Combined with the higher-degree theorem, this gives vanishing in every positive
degree over an arbitrary commutative ring, including nonreduced and zero rings.
-/
@[expose] public section
open Quillen


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open Opposite
namespace AlgebraicGeometry.Scheme.ProjectiveLine
open PolynomialLaurent
variable (R : CommRingCat.{u})
/-- Original Laurent sections identified with sections on the actual chart intersection. -/
def overlapSectionsIso : Γ(Spec (.of (LaurentPolynomial R)), ⊤) ≅
    Γ(twoChartLine R, (plusChart R).opensRange ⊓ (minusChart R).opensRange) :=
  IsOpenImmersion.ΓIsoTop (laurentPlus R ≫ plusChart R) ≪≫
    (twoChartLine R).presheaf.mapIso (eqToIso (chart_ranges_inter R)).op

/-- The positive chart identification preserves its original restriction. -/
lemma plus_restriction_overlap :
    (twoChartLine R).presheaf.map (homOfLE inf_le_left).op ≫ (overlapSectionsIso R).inv =
      (IsOpenImmersion.ΓIsoTop (plusChart R)).inv ≫ (laurentPlus R).appTop := by
  simp only [overlapSectionsIso, Iso.trans_inv, Functor.mapIso_inv]
  rw [← Category.assoc, ← Functor.map_comp]
  exact restrict_gammaIsoTop_inv _ _ (by rw [← chart_ranges_inter]; exact inf_le_left)

/-- The negative chart identification preserves its original restriction. -/
lemma minus_restriction_overlap :
    (twoChartLine R).presheaf.map (homOfLE inf_le_right).op ≫ (overlapSectionsIso R).inv =
      (IsOpenImmersion.ΓIsoTop (minusChart R)).inv ≫ (laurentMinus R).appTop := by
  simp only [overlapSectionsIso, Iso.trans_inv, Functor.mapIso_inv]
  rw [← Category.assoc, ← Functor.map_comp]
  rw [gammaIsoTop_inv, gammaIsoTop_inv, Scheme.Hom.map_appLE]
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  simp only [overlap_equation]
  rfl

open AlgebraicGeometry.Scheme.Modules.TwoOpen
/-- The canonical section identifications intertwine the literal signed differences. -/
lemma structureSheaf_difference_coordinates
    (a : Γ(SheafOfModules.unit (twoChartLine R).ringCatSheaf, (plusChart R).opensRange))
    (b : Γ(SheafOfModules.unit (twoChartLine R).ringCatSheaf, (minusChart R).opensRange)) :
    (overlapSectionsIso R).inv.hom
      (difference (SheafOfModules.unit (twoChartLine R).ringCatSheaf)
        (plusChart R).opensRange (minusChart R).opensRange (a, b)) =
    chartSectionsDifference R
      ((IsOpenImmersion.ΓIsoTop (plusChart R)).inv.hom a,
       (IsOpenImmersion.ΓIsoTop (minusChart R)).inv.hom b) := by
  change (overlapSectionsIso R).inv.hom
    (((twoChartLine R).presheaf.map (homOfLE inf_le_left).op).hom a -
     ((twoChartLine R).presheaf.map (homOfLE inf_le_right).op).hom b) = _
  rw [map_sub]
  have hp := congrArg (fun f => CommRingCat.Hom.hom f a) (plus_restriction_overlap R)
  have hm := congrArg (fun f => CommRingCat.Hom.hom f b) (minus_restriction_overlap R)
  exact congrArg₂ (fun x y => x - y) hp hm

/-- Every original structure-sheaf section on the intersection is a chart difference. -/
theorem structureSheaf_difference_surjective :
    Function.Surjective (difference (SheafOfModules.unit (twoChartLine R).ringCatSheaf)
      (plusChart R).opensRange (minusChart R).opensRange) := by
  intro z
  obtain ⟨⟨a, b⟩, hab⟩ := chartSectionsDifference_surjective R
    ((overlapSectionsIso R).inv.hom z)
  refine ⟨((IsOpenImmersion.ΓIsoTop (plusChart R)).hom.hom a,
    (IsOpenImmersion.ΓIsoTop (minusChart R)).hom.hom b), ?_⟩
  apply (ConcreteCategory.bijective_of_isIso (overlapSectionsIso R).inv).1
  change (overlapSectionsIso R).inv.hom _ = (overlapSectionsIso R).inv.hom z
  rw [structureSheaf_difference_coordinates]
  simpa using hab

/-- First derived global sections of the actual structure module sheaf vanish. -/
theorem isZero_rightDerived_structureSheaf_one :
    IsZero (((sectionsFunctor (twoChartLine R) ⊤).rightDerived 1).obj
      (SheafOfModules.unit (twoChartLine R).ringCatSheaf)) := by
  have : (SheafOfModules.unit (twoChartLine R).ringCatSheaf).IsQuasicoherent :=
    isQuasicoherent_unit _
  exact AlgebraicGeometry.Scheme.Modules.twoAffine_isZero_rightDerived_one_of_difference_surjective
    _ (plusChart R) (minusChart R) (chart_ranges_cover R)
    (structureSheaf_difference_surjective R)

/-- All positive derived global sections of the original structure module sheaf vanish. -/
theorem isZero_rightDerived_structureSheaf_succ (n : ℕ) :
    IsZero (((sectionsFunctor (twoChartLine R) ⊤).rightDerived (n + 1)).obj
      (SheafOfModules.unit (twoChartLine R).ringCatSheaf)) := by
  cases n with
  | zero => exact isZero_rightDerived_structureSheaf_one R
  | succ n =>
    have : (SheafOfModules.unit (twoChartLine R).ringCatSheaf).IsQuasicoherent :=
      isQuasicoherent_unit _
    exact isZero_rightDerived_globalSections_add_two R _ n

end AlgebraicGeometry.Scheme.ProjectiveLine
