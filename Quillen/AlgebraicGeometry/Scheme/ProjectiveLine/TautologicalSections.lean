/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.Tautological
public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.StructureSheafCohomology
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.RestrictionSections

/-!
# Original sections of the tautological line

The original two chart trivializations identify actual sections with polynomial
sections. In positive Laurent coordinates the signed restriction difference is
exactly `difference R (-1)`, hence bijective. All maps are original sheaf and
scheme restrictions, and the base ring may be the zero ring.
-/
@[expose] public section
open Quillen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.ProjectiveLine
open PolynomialLaurent AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.TwoOpen
variable (R : CommRingCat.{u})

/-- The original positive-chart sections in the chosen actual trivialization. -/
def tautologicalPlusSectionsIso :
    Γ(tautologicalLine R, (plusChart R).opensRange) ≅
      AddCommGrpCat.of Γ(Spec (.of (Polynomial R)), ⊤) :=
  ((restrictedSectionsIso (plusChart R)).app (tautologicalLine R)).symm ≪≫
    (sectionsFunctor _ ⊤).mapIso (tautologicalLinePlusIso R)

/-- The original negative-chart sections in the chosen actual trivialization. -/
def tautologicalMinusSectionsIso :
    Γ(tautologicalLine R, (minusChart R).opensRange) ≅
      AddCommGrpCat.of Γ(Spec (.of (Polynomial R)), ⊤) :=
  ((restrictedSectionsIso (minusChart R)).app (tautologicalLine R)).symm ≪≫
    (sectionsFunctor _ ⊤).mapIso (tautologicalLineMinusIso R)

/-- The positive-chart trivialization pulled back to the original Laurent overlap. -/
def tautologicalLaurentIso :
    (tautologicalLine R).restrict (laurentPlus R ≫ plusChart R) ≅
      SheafOfModules.unit (Spec (.of (LaurentPolynomial R))).ringCatSheaf :=
  (Scheme.Modules.restrictFunctorComp (laurentPlus R) (plusChart R)).app
      (tautologicalLine R) ≪≫
    (Scheme.Modules.restrictFunctor (laurentPlus R)).mapIso (tautologicalLinePlusIso R) ≪≫
      Scheme.Modules.restrictUnitIso (laurentPlus R)

/-- The original intersection sections in positive Laurent coordinates. -/
def tautologicalOverlapSectionsIso :
    Γ(tautologicalLine R, (plusChart R).opensRange ⊓ (minusChart R).opensRange) ≅
      AddCommGrpCat.of Γ(Spec (.of (LaurentPolynomial R)), ⊤) :=
  (tautologicalLine R).presheaf.mapIso (eqToIso (chart_ranges_inter R).symm).op ≪≫
    ((restrictedSectionsIso (laurentPlus R ≫ plusChart R)).app (tautologicalLine R)).symm ≪≫
      (sectionsFunctor _ ⊤).mapIso (tautologicalLaurentIso R)

/-- Positive Laurent coordinates preserve the literal positive-chart restriction. -/
lemma tautologicalPlus_restriction_overlap :
    (tautologicalLine R).presheaf.map (homOfLE inf_le_left).op ≫
        (tautologicalOverlapSectionsIso R).hom =
      (tautologicalPlusSectionsIso R).hom ≫
        AddCommGrpCat.ofHom (laurentPlus R).appTop.hom.toAddMonoidHom := by
  dsimp only [tautologicalOverlapSectionsIso, tautologicalPlusSectionsIso,
    tautologicalLaurentIso, restrictedSectionsIso, sectionsFunctor,
    NatIso.ofComponents, Iso.app, Iso.trans, Iso.symm, Functor.mapIso]
  simp only [Scheme.Modules.Hom.comp_app,
    Scheme.Modules.restrictFunctorComp_hom_app_app, Category.assoc]
  simp only [Scheme.Modules.restrictAppIso, Iso.refl_inv,
    ← Functor.map_comp_assoc]
  erw [Category.id_comp, Category.id_comp]
  rw [← Functor.map_comp_assoc]
  ext x
  change ((laurentPlus R).appIso ⊤).hom.hom
    (((tautologicalLinePlusIso R).hom.app ((laurentPlus R) ''ᵁ ⊤)).hom
      (((tautologicalLine R).presheaf.map
        (homOfLE ((plusChart R).image_le_opensRange ((laurentPlus R) ''ᵁ ⊤))).op).hom x)) =
    (laurentPlus R).appTop.hom (((tautologicalLinePlusIso R).hom.app ⊤).hom
      (((tautologicalLine R).presheaf.map
        (homOfLE ((plusChart R).image_le_opensRange ⊤)).op).hom x))
  have hn := (tautologicalLinePlusIso R).hom.mapPresheaf.naturality
    (homOfLE (show (laurentPlus R) ''ᵁ ⊤ ≤ ⊤ from le_top)).op
  have hx := congrArg
    (fun f => AddCommGrpCat.Hom.hom f
      (((tautologicalLine R).presheaf.map
        (homOfLE ((plusChart R).image_le_opensRange ⊤)).op).hom x)) hn
  change ((tautologicalLinePlusIso R).hom.app ((laurentPlus R) ''ᵁ ⊤)).hom
      (((tautologicalLine R).presheaf.map
        (homOfLE ((plusChart R).image_mono le_top)).op).hom
          (((tautologicalLine R).presheaf.map
            (homOfLE ((plusChart R).image_le_opensRange ⊤)).op).hom x)) =
    ((Spec (.of (Polynomial R))).presheaf.map (homOfLE le_top).op).hom
      (((tautologicalLinePlusIso R).hom.app ⊤).hom
        (((tautologicalLine R).presheaf.map
          (homOfLE ((plusChart R).image_le_opensRange ⊤)).op).hom x)) at hx
  rw [← AddCommGrpCat.comp_apply, ← Functor.map_comp] at hx
  erw [hx]
  change (((Spec (.of (Polynomial R))).presheaf.map (homOfLE le_top).op ≫
    ((laurentPlus R).appIso ⊤).hom).hom _) = _
  rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
  rfl

/-- The first actual global coordinate of the tautological inclusion. -/
def tautologicalFirstCoordinate : tautologicalLine R ⟶
    SheafOfModules.unit (twoChartLine R).ringCatSheaf :=
  tautologicalLineInclusion R ≫ prod.fst

/-- The second actual global coordinate of the tautological inclusion. -/
def tautologicalSecondCoordinate : tautologicalLine R ⟶
    SheafOfModules.unit (twoChartLine R).ringCatSheaf :=
  tautologicalLineInclusion R ≫ prod.snd

/-- The first coordinate is the chosen positive-chart trivialization. -/
lemma tautologicalFirstCoordinate_plus :
    (Scheme.Modules.restrictFunctor (plusChart R)).map (tautologicalFirstCoordinate R) ≫
      (Scheme.Modules.restrictUnitIso (plusChart R)).hom =
        (tautologicalLinePlusIso R).hom := by
  rw [tautologicalFirstCoordinate, Functor.map_comp, tautologicalLineInclusion_plus]
  have h := congrArg (fun k => (tautologicalLinePlusIso R).hom ≫ k ≫
    (Scheme.Modules.restrictUnitIso (plusChart R)).hom)
    (firstColumn_fst (plusChart R) (polynomialCoordinate R))
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h

/-- The second coordinate is the chosen negative-chart trivialization. -/
lemma tautologicalSecondCoordinate_minus :
    (Scheme.Modules.restrictFunctor (minusChart R)).map (tautologicalSecondCoordinate R) ≫
      (Scheme.Modules.restrictUnitIso (minusChart R)).hom =
        (tautologicalLineMinusIso R).hom := by
  rw [tautologicalSecondCoordinate, Functor.map_comp, tautologicalLineInclusion_minus]
  have h := congrArg (fun k => (tautologicalLineMinusIso R).hom ≫ k ≫
    (Scheme.Modules.restrictUnitIso (minusChart R)).hom)
    (secondColumn_snd (minusChart R) (polynomialCoordinate R))
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h

/-- The first coordinate on the negative chart multiplies by its original coordinate. -/
lemma tautologicalFirstCoordinate_minus :
    (Scheme.Modules.restrictFunctor (minusChart R)).map (tautologicalFirstCoordinate R) ≫
      (Scheme.Modules.restrictUnitIso (minusChart R)).hom =
        (tautologicalLineMinusIso R).hom ≫ unitMul _ (polynomialCoordinate R) := by
  rw [tautologicalFirstCoordinate, Functor.map_comp, tautologicalLineInclusion_minus]
  have h := congrArg (fun k => (tautologicalLineMinusIso R).hom ≫ k ≫
    (Scheme.Modules.restrictUnitIso (minusChart R)).hom)
    (secondColumn_fst (minusChart R) (polynomialCoordinate R))
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h

/-- Positive section coordinates are induced by the original first global coordinate. -/
lemma tautologicalPlusSectionsIso_firstCoordinate :
    (tautologicalPlusSectionsIso R).hom =
      (tautologicalFirstCoordinate R).app (plusChart R).opensRange ≫
        AddCommGrpCat.ofHom (IsOpenImmersion.ΓIsoTop (plusChart R)).inv.hom.toAddMonoidHom :=
  trivializedOpenSectionsIso_hom _ _ _ _ (tautologicalFirstCoordinate_plus R)

/-- Negative section coordinates are induced by the original second global coordinate. -/
lemma tautologicalMinusSectionsIso_secondCoordinate :
    (tautologicalMinusSectionsIso R).hom =
      (tautologicalSecondCoordinate R).app (minusChart R).opensRange ≫
        AddCommGrpCat.ofHom (IsOpenImmersion.ΓIsoTop (minusChart R)).inv.hom.toAddMonoidHom :=
  trivializedOpenSectionsIso_hom _ _ _ _ (tautologicalSecondCoordinate_minus R)

/-- The positive Laurent trivialization comes from the original first coordinate. -/
lemma tautologicalFirstCoordinate_laurent :
    (Scheme.Modules.restrictFunctor (laurentPlus R ≫ plusChart R)).map
        (tautologicalFirstCoordinate R) ≫
      (Scheme.Modules.restrictUnitIso (laurentPlus R ≫ plusChart R)).hom =
        (tautologicalLaurentIso R).hom := by
  have hn := (Scheme.Modules.restrictFunctorComp (laurentPlus R) (plusChart R)).hom.naturality
    (tautologicalFirstCoordinate R)
  dsimp only [Functor.comp_map] at hn
  rw [← restrictUnitIso_comp (laurentPlus R) (plusChart R), ← Category.assoc, ← Category.assoc, hn]
  simp only [tautologicalLaurentIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  rw [Category.assoc, Category.assoc, ← Functor.map_comp_assoc, tautologicalFirstCoordinate_plus]

/-- The overlap section isomorphism retains the original global first-coordinate arrow. -/
lemma tautologicalOverlapSectionsIso_firstCoordinate :
    (tautologicalOverlapSectionsIso R).hom =
      (tautologicalFirstCoordinate R).app
          ((plusChart R).opensRange ⊓ (minusChart R).opensRange) ≫
        AddCommGrpCat.ofHom (overlapSectionsIso R).inv.hom.toAddMonoidHom := by
  have h := trivializedOpenSectionsIso_hom
    (laurentPlus R ≫ plusChart R) (tautologicalLine R)
    (tautologicalLaurentIso R) (tautologicalFirstCoordinate R)
    (tautologicalFirstCoordinate_laurent R)
  change (tautologicalLine R).presheaf.map (eqToIso (chart_ranges_inter R).symm).op.hom ≫
    (trivializedOpenSectionsIso (laurentPlus R ≫ plusChart R) (tautologicalLine R)
      (tautologicalLaurentIso R)).hom = _
  rw [h, ← Category.assoc]
  erw [(tautologicalFirstCoordinate R).mapPresheaf.naturality]
  rfl

/-- The first-coordinate section map has its literal negative-chart scalar factor. -/
lemma tautologicalFirstCoordinate_minusSections :
    (tautologicalFirstCoordinate R).app (minusChart R).opensRange ≫
      AddCommGrpCat.ofHom (IsOpenImmersion.ΓIsoTop (minusChart R)).inv.hom.toAddMonoidHom =
    (tautologicalMinusSectionsIso R).hom ≫
      Scheme.Modules.Hom.app (unitMul _ (polynomialCoordinate R)) ⊤ := by
  have h := restrictedSectionsIso_inv_map_unit (minusChart R) (tautologicalLine R)
    (tautologicalFirstCoordinate R)
  rw [tautologicalFirstCoordinate_minus, Functor.map_comp] at h
  exact h

/-- Negative restriction retains the original coordinate multiplication on the Laurent overlap. -/
lemma tautologicalMinus_restriction_overlap :
    (tautologicalLine R).presheaf.map (homOfLE inf_le_right).op ≫
        (tautologicalOverlapSectionsIso R).hom =
      (tautologicalMinusSectionsIso R).hom ≫
        Scheme.Modules.Hom.app (unitMul _ (polynomialCoordinate R)) ⊤ ≫
          AddCommGrpCat.ofHom (laurentMinus R).appTop.hom.toAddMonoidHom := by
  rw [tautologicalOverlapSectionsIso_firstCoordinate, ← Category.assoc]
  erw [(tautologicalFirstCoordinate R).mapPresheaf.naturality]
  rw [Category.assoc]
  have hm :
      (Scheme.Modules.presheaf
        (SheafOfModules.unit (twoChartLine R).ringCatSheaf)).map
          (homOfLE inf_le_right).op ≫
        AddCommGrpCat.ofHom (overlapSectionsIso R).inv.hom.toAddMonoidHom =
      AddCommGrpCat.ofHom (IsOpenImmersion.ΓIsoTop (minusChart R)).inv.hom.toAddMonoidHom ≫
        AddCommGrpCat.ofHom (laurentMinus R).appTop.hom.toAddMonoidHom :=
    congrArg (fun f => AddCommGrpCat.ofHom (CommRingCat.Hom.hom f).toAddMonoidHom)
      (minus_restriction_overlap R)
  erw [hm]
  rw [← Category.assoc]
  erw [tautologicalFirstCoordinate_minusSections]
  rw [Category.assoc]

lemma tautological_difference_chart_coordinates
    (a : Γ(tautologicalLine R, (plusChart R).opensRange))
    (b : Γ(tautologicalLine R, (minusChart R).opensRange)) :
    (tautologicalOverlapSectionsIso R).hom
        (difference (tautologicalLine R) (plusChart R).opensRange
          (minusChart R).opensRange (a, b)) =
      chartSectionsDifference R
        ((tautologicalPlusSectionsIso R).hom a,
          (tautologicalMinusSectionsIso R).hom b * polynomialCoordinate R) := by
  have hp := congrArg (fun f => AddCommGrpCat.Hom.hom f a)
    (tautologicalPlus_restriction_overlap R)
  have hm := congrArg (fun f => AddCommGrpCat.Hom.hom f b)
    (tautologicalMinus_restriction_overlap R)
  rw [difference_apply, map_sub]
  simp only [chartSectionsDifference, AddMonoidHom.sub_apply, AddMonoidHom.comp_apply]
  apply congrArg₂ (fun x y => x - y)
  · exact hp
  · change _ = (laurentMinus R).appTop.hom
      ((tautologicalMinusSectionsIso R).hom b *
        (((Spec (.of (Polynomial R))).presheaf.map (𝟙 (op ⊤))).hom
          (polynomialCoordinate R))) at hm
    erw [CategoryTheory.Functor.map_id] at hm
    exact hm

lemma tautological_difference_coordinates
    (a : Γ(tautologicalLine R, (plusChart R).opensRange))
    (b : Γ(tautologicalLine R, (minusChart R).opensRange)) :
    (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).hom.hom
        ((tautologicalOverlapSectionsIso R).hom
          (difference (tautologicalLine R) (plusChart R).opensRange
            (minusChart R).opensRange (a, b))) =
      Quillen.PolynomialLaurentCech.difference R (-1)
        ((Scheme.ΓSpecIso (.of (Polynomial R))).hom.hom ((tautologicalPlusSectionsIso R).hom a),
          (Scheme.ΓSpecIso (.of (Polynomial R))).hom.hom
            ((tautologicalMinusSectionsIso R).hom b)) := by
  rw [tautological_difference_chart_coordinates, chartSectionsDifference_coordinates, map_mul]
  have hc : (Scheme.ΓSpecIso (.of (Polynomial R))).hom.hom (polynomialCoordinate R) =
      Polynomial.X := by simp [polynomialCoordinate]
  rw [hc]
  have h := LinearMap.congr_fun (Quillen.PolynomialLaurentCech.difference_shiftSecond R 0)
    ((Scheme.ΓSpecIso (.of (Polynomial R))).hom.hom ((tautologicalPlusSectionsIso R).hom a),
      (Scheme.ΓSpecIso (.of (Polynomial R))).hom.hom ((tautologicalMinusSectionsIso R).hom b))
  simpa only [LinearMap.comp_apply, Quillen.PolynomialLaurentCech.shiftSecond_apply,
    zero_sub, mul_comm] using h

/-- Every original overlap section is a difference of original tautological chart sections. -/
theorem tautological_difference_surjective :
    Function.Surjective (difference (tautologicalLine R)
      (plusChart R).opensRange (minusChart R).opensRange) := by
  intro z
  obtain ⟨⟨a, b⟩, hab⟩ := Quillen.PolynomialLaurentCech.difference_surjective R (-1) le_rfl
    ((Scheme.ΓSpecIso (.of (LaurentPolynomial R))).hom.hom
      ((tautologicalOverlapSectionsIso R).hom z))
  refine ⟨((tautologicalPlusSectionsIso R).inv ((Scheme.ΓSpecIso (.of (Polynomial R))).inv a),
    (tautologicalMinusSectionsIso R).inv ((Scheme.ΓSpecIso (.of (Polynomial R))).inv b)), ?_⟩
  apply (ConcreteCategory.bijective_of_isIso (tautologicalOverlapSectionsIso R).hom).1
  apply (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).hom).1
  rw [tautological_difference_coordinates]
  simpa using hab

/-- Original tautological chart sections are uniquely determined by their signed difference. -/
theorem tautological_difference_injective :
    Function.Injective (difference (tautologicalLine R)
      (plusChart R).opensRange (minusChart R).opensRange) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have hco := congrArg (fun z => (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).hom.hom
    ((tautologicalOverlapSectionsIso R).hom z)) h
  rw [tautological_difference_coordinates, tautological_difference_coordinates] at hco
  have hab := Quillen.PolynomialLaurentCech.difference_neg_one_injective R hco
  apply Prod.ext
  · apply (ConcreteCategory.bijective_of_isIso (tautologicalPlusSectionsIso R).hom).1
    apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (Polynomial R))).hom).1
    exact congrArg Prod.fst hab
  · apply (ConcreteCategory.bijective_of_isIso (tautologicalMinusSectionsIso R).hom).1
    apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (Polynomial R))).hom).1
    exact congrArg Prod.snd hab


end AlgebraicGeometry.Scheme.ProjectiveLine
