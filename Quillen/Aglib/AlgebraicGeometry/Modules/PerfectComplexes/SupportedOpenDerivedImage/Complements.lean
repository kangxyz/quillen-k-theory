/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.SupportedOpenDerivedImage.Exact
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic

/-!
# Actual supported complements and wrapper equivalence

The qcqs supported complement supplies the displayed coproduct membership. The nested and
direct chain categories are literally equivalent, retaining their actual support and
inclusions.
-/
@[expose] public section



open CategoryTheory.ExactCategory



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
attribute [local instance] Scheme.Modules.standardHasDerivedCategory
namespace Quillen.PerfectComplexes.SupportedOpenDerivedImage
attribute [local instance] HasDerivedCategory.standard Abelian.hasFiniteBiproducts
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

/-- The full category of supported perfect complexes in the actual supported
derived restriction image. -/
abbrev Obj := (objects j T).FullSubcategory

/-- Actual complex complements give membership of the original chosen
categorical coproduct through its genuine colimit comparison. -/
theorem coprod_complement_of_complex_complement [HasBinaryCoproducts ((perfectSupported (j ⁻¹ᵁ
  T).ι).FullSubcategory)]
    (A : (perfectSupported (j ⁻¹ᵁ T).ι).FullSubcategory) (C : CochainComplex U.Modules ℤ)
      (hC : perfectSupported (j
      ⁻¹ᵁ T).ι C)
    (hAC : complexObjects j T (C ⊞ A.obj)) :
    ∃ B : (perfectSupported (j ⁻¹ᵁ T).ι).FullSubcategory, objects j T (A ⨿ B) := by
  let B : (perfectSupported (j ⁻¹ᵁ T).ι).FullSubcategory := ⟨C, hC⟩
  let BSum : (perfectSupported (j ⁻¹ᵁ T).ι).FullSubcategory := ⟨A.obj ⊞ B.obj,
    (abelianExactStructure _).prop_biprod _ A.property B.property⟩
  let il : A ⟶ BSum := ObjectProperty.homMk biprod.inl
  let ir : B ⟶ BSum := ObjectProperty.homMk biprod.inr
  have ht : IsColimit (BinaryCofan.mk il ir) := by
    refine BinaryCofan.IsColimit.mk _ (fun f g => ObjectProperty.homMk (biprod.desc f.hom g.hom)) ?_
      ?_ ?_
    · intro S f g
      apply ObjectProperty.hom_ext
      exact biprod.inl_desc _ _
    · intro S f g
      apply ObjectProperty.hom_ext
      exact biprod.inr_desc _ _
    · intro S f g m hm hn
      apply ObjectProperty.hom_ext
      apply biprod.hom_ext'
      · exact (congrArg (fun k => k.hom) hm).trans (biprod.inl_desc _ _).symm
      · exact (congrArg (fun k => k.hom) hn).trans (biprod.inr_desc _ _).symm
  let e : A ⨿ B ≅ BSum := (coprodIsCoprod A B).coconePointUniqueUpToIso ht
  have hT : complexObjects j T BSum.obj := (complexObjects_iff_of_derivedIso j T
    ((DerivedCategory.Q (C := U.Modules)).mapIso (biprod.braiding A.obj C))).mpr hAC
  exact ⟨B, (complexObjects_iff_of_derivedIso j T
    ((DerivedCategory.Q (C := U.Modules)).mapIso ((perfectSupported
      (j ⁻¹ᵁ T).ι).ι.mapIso e))).mpr hT⟩

/-- Actual supported global complements provide coproduct density with
no further extension or strictification premise. -/
lemma global_complement [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
    (hT : IsCompact (T : Set X))
    [HasBinaryCoproducts (perfectSupported (j ⁻¹ᵁ T).ι).FullSubcategory]
    (A : (perfectSupported (j ⁻¹ᵁ T).ι).FullSubcategory) :
    ∃ B : (perfectSupported (j ⁻¹ᵁ T).ι).FullSubcategory, objects j T (A ⨿ B) := by
  obtain ⟨C, hC, hAC⟩ := exists_supported_perfect_complement j T hT A.obj A.property
  exact coprod_complement_of_complex_complement j T A C hC hAC

end Quillen.PerfectComplexes.SupportedOpenDerivedImage

end

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Quillen.PerfectComplexes.SupportedOpenDerivedImage
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

/-- Forget only the redundant perfect-object wrapper. -/
def flatten : Obj j T ⥤ ComplexObj j T where
  obj A := ⟨A.obj.obj, A.property⟩
  map f := (complexObjects j T).homMk f.hom.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Restore the proved local perfectness of the same original complex. -/
def nest : ComplexObj j T ⥤ Obj j T where
  obj A := ⟨⟨A.obj, perfectSupported_of_mem j T A.property⟩, A.property⟩
  map f := (objects j T).homMk ((perfectSupported (j ⁻¹ᵁ T).ι).homMk f.hom)
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem flatten_comp_nest : flatten j T ⋙ nest j T = 𝟭 (Obj j T) := rfl
@[simp] theorem nest_comp_flatten : nest j T ⋙ flatten j T = 𝟭 (ComplexObj j T) := rfl

/-- A genuine equivalence on unchanged original complexes and chain maps. -/
def flattenEquivalence : Obj j T ≌ ComplexObj j T where
  functor := flatten j T
  inverse := nest j T
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
    (by intros; simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)
    (by intros; simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)

/-- Flattening retains the literal original perfect-complex inclusion. -/
@[simp] theorem flatten_comp_inclusion : flatten j T ⋙ inclusion j T = (objects j T).ι := rfl
@[simp] theorem nest_comp_inclusion : nest j T ⋙ (objects j T).ι = inclusion j T := rfl

end Quillen.PerfectComplexes.SupportedOpenDerivedImage

end


end
