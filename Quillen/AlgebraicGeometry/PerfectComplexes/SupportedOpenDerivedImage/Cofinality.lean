/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpenDerivedImage.Structure
public import Quillen.CategoryTheory.Abelian.ZeroPushout
public import Quillen.Waldhausen.Cofinality.GeneralDense
public import Quillen.Waldhausen.Functoriality.ExactEquivalence
public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpenDerivedImage.Approximation

/-!
# Genuine supported image density and cofinality

The actual qcqs supported perfect complement supplies DenseCofiberData on
the existing supported target. The nested object presentation is exactly
equivalent to the direct complex image. Its original inclusion is bijective
on positive K-groups and injective on K0. Composing with actual relative
corestriction retains precisely perfectSupportedOpenKRestrict. Structural
lemmas retain their explicit genuine roof, density and joint inputs.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace Quillen.PerfectComplexes.SupportedOpenDerivedImage
open Waldhausen
attribute [local instance] HasDerivedCategory.standard Abelian.hasFiniteBiproducts
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

/-- The full category of supported perfect complexes in the actual supported
derived restriction image. -/
abbrev Obj := (objects j T).FullSubcategory

/-- The actual chosen supported zero belongs to the supported restriction image. -/
lemma zero_mem : objects j T (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).zero :=
  (derivedObjects j T).prop_of_isZero ((toDerived U).map_isZero
    ((perfectSupported (j ⁻¹ᵁ T).ι).ι.map_isZero
      (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).isZero))

/-- Genuine cofibration pushouts yield original short exact sequences and
hence extension membership in the unchanged chain category. -/
theorem extension_mem (hroof : OpenDerivedImage.HasSupportedDerivedRoofs j T)
    {A B Q : (perfectSupported (j ⁻¹ᵁ T).ι).FullSubcategory} {i : A ⟶ B} {q : B ⟶ Q}
    (hi : (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).cof i)
    (h : IsPushout i ((perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).isZero.from_ A) q
      ((perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).isZero.to_ Q))
    (hA : objects j T A) (hQ : objects j T Q) : objects j T B := by
  have hp := (complexSubcategory_inclusion_exact (perfectSupported (j ⁻¹ᵁ T).ι)).pushout hi h
  have : Mono ((perfectSupported (j ⁻¹ᵁ T).ι).ι.map i) :=
    (complexSubcategory_inclusion_exact (perfectSupported (j ⁻¹ᵁ T).ι)).cofibration i hi
  obtain ⟨z, hz⟩ := Quillen.Abelian.shortExact_of_mono_pushout_zero
    ((perfectSupported (j ⁻¹ᵁ T).ι).ι.map_isZero (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).isZero) hp
  exact complexObjects_of_shortExact j T hroof hz hA hQ

/-- The original cofiber is retained in the quotient closure statement. -/
theorem quotient_mem (hroof : OpenDerivedImage.HasSupportedDerivedRoofs j T)
    {A B Q : (perfectSupported (j ⁻¹ᵁ T).ι).FullSubcategory} {i : A ⟶ B} {q : B ⟶ Q}
    (hi : (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).cof i)
    (h : IsPushout i ((perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).isZero.from_ A) q
      ((perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).isZero.to_ Q))
    (hA : objects j T A) (hB : objects j T B) : objects j T Q := by
  have hp := (complexSubcategory_inclusion_exact (perfectSupported (j ⁻¹ᵁ T).ι)).pushout hi h
  have : Mono ((perfectSupported (j ⁻¹ᵁ T).ι).ι.map i) :=
    (complexSubcategory_inclusion_exact (perfectSupported (j ⁻¹ᵁ T).ι)).cofibration i hi
  obtain ⟨z, hz⟩ := Quillen.Abelian.shortExact_of_mono_pushout_zero
    ((perfectSupported (j ⁻¹ᵁ T).ι).ι.map_isZero (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).isZero) hp
  exact complexObjects_quotient_of_shortExact j T hroof hz hA hB

/-- Actual complex complements give membership of the original chosen
categorical coproduct through its genuine colimit comparison. -/
theorem coprod_complement_of_complex_complement [HasBinaryCoproducts ((perfectSupported (j ⁻¹ᵁ
  T).ι).FullSubcategory)]
    (A : (perfectSupported (j ⁻¹ᵁ T).ι).FullSubcategory) (C : Complex U) (hC : perfectSupported (j
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
    ((toDerived U).mapIso (biprod.braiding A.obj C))).mpr hAC
  exact ⟨B, (complexObjects_iff_of_derivedIso j T
    ((toDerived U).mapIso ((perfectSupported (j ⁻¹ᵁ T).ι).ι.mapIso e))).mpr hT⟩

/-- Actual supported global complements provide coproduct density with
no further extension or strictification premise. -/
lemma global_complement [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
    (hT : IsCompact (T : Set X))
    [HasBinaryCoproducts (perfectSupported (j ⁻¹ᵁ T).ι).FullSubcategory]
    (A : (perfectSupported (j ⁻¹ᵁ T).ι).FullSubcategory) :
    ∃ B : (perfectSupported (j ⁻¹ᵁ T).ι).FullSubcategory, objects j T (A ⨿ B) := by
  obtain ⟨C, hC, hAC⟩ := exists_supported_perfect_complement j T hT A.obj A.property
  exact coprod_complement_of_complex_complement j T A C hC hAC

/-- The prescribed-support image has genuine standard dense cofiber data. -/
theorem globalDenseData [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
    (hT : IsCompact (T : Set X)) (hroof : OpenDerivedImage.HasSupportedDerivedRoofs j T)
    [HasBinaryCoproducts (perfectSupported (j ⁻¹ᵁ T).ι).FullSubcategory] :
    Cofinality.DenseCofiberData (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι) (objects j T) where
  zero := zero_mem j T
  weak f hf := by
    have : QuasiIso f.hom := hf
    exact complexObjects_iff_of_quasiIso j T f.hom
  extension := extension_mem j T hroof
  quotient := quotient_mem j T hroof
  complement := global_complement j T hT

end Quillen.PerfectComplexes.SupportedOpenDerivedImage

end

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Quillen.PerfectComplexes.SupportedOpenDerivedImage
open Waldhausen
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

local instance : (flatten j T).IsEquivalence := (flattenEquivalence j T).isEquivalence_functor
local instance : (nest j T).IsEquivalence := (flattenEquivalence j T).isEquivalence_inverse

/-- Flattening retains the literal original perfect-complex inclusion. -/
@[simp] theorem flatten_comp_inclusion : flatten j T ⋙ inclusion j T = (objects j T).ι := rfl
@[simp] theorem nest_comp_inclusion : nest j T ⋙ (objects j T).ι = inclusion j T := rfl

variable [Fact (OpenDerivedImage.HasSupportedDerivedRoofs j T)] [HasBinaryCoproducts
  ((perfectSupported (j ⁻¹ᵁ T).ι).FullSubcategory)]
  (h : Cofinality.DenseCofiberData (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι) (objects j T))

/-- The inherited perfect cofibrations are exactly those on the flattened image. -/
theorem flatten_exact : IsExact h.waldhausenStructure.cof h.waldhausenStructure.weq
    (complexWaldhausen j T).cof (complexWaldhausen j T).weq (flatten j T) where
  zero hz := IsZero.of_full_of_faithful_of_isZero (nest j T) _ hz
  cofibration f hf := (inclusion_cof_iff j T ((flatten j T).map f)).mp hf
  weak _ hf := hf
  pushout _ hp := hp.map (flatten j T)

/-- The genuine inverse is exact for the same original weak arrows and cofibrations. -/
theorem nest_exact : IsExact (complexWaldhausen j T).cof (complexWaldhausen j T).weq
    h.waldhausenStructure.cof h.waldhausenStructure.weq (nest j T) where
  zero hz := IsZero.of_full_of_faithful_of_isZero (flatten j T) _ hz
  cofibration f hf := (inclusion_exact j T).cofibration f hf
  weak _ hf := hf
  pushout _ hp := hp.map (nest j T)

/-- All connective K-groups agree by an actual exact equivalence. -/
def flattenKEquiv (n : ℕ) : h.waldhausenStructure.K n ≃* (complexWaldhausen j T).K n :=
  KEquivOfExactEquivalence _ _ (flattenEquivalence j T) (flatten_exact j T h) (nest_exact j T h) n

/-- The forward K comparison is the actual original flattening map. -/
@[simp] theorem flattenKEquiv_toMonoidHom (n : ℕ) :
    (flattenKEquiv j T h n :
      h.waldhausenStructure.K n →* (complexWaldhausen j T).K n) =
        KMap (flatten_exact j T h) n := rfl

/-- Original inclusion commutes with the flattening K comparison. -/
theorem flattenKEquiv_inclusion (n : ℕ) :
    (KMap (inclusion_exact j T) n).comp (flattenKEquiv j T h n) =
      KMap h.inclusion_exact n := by
  rw [flattenKEquiv_toMonoidHom, Quillen.Waldhausen.KMap_comp_KMap]

include h in
/-- Cofinality of the original dense image gives the original flattened inclusion in positive
  degrees. -/
theorem inclusion_KMap_succ_bijective
    (D : Fibration.RowFactorization.JointData (.refl (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι)))
    (hs : Fibration.RowFactorization.SecondEndpointSection (.refl (perfectSupportedWaldhausen (j ⁻¹ᵁ
      T).ι)) D)
    (n : ℕ) : Function.Bijective (KMap (inclusion_exact j T) (n+1)) := by
  have hcomp := h.inclusion_KMap_succ_bijective_general D hs n
  rw [← flattenKEquiv_inclusion j T h (n+1)] at hcomp
  exact ((flattenKEquiv j T h (n+1)).bijective.of_comp_iff _).mp hcomp

include h in
/-- The original flattened inclusion is injective in every connective degree, including zero. -/
theorem inclusion_KMap_injective
    (D : Fibration.RowFactorization.JointData (.refl (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι)))
    (hs : Fibration.RowFactorization.SecondEndpointSection (.refl (perfectSupportedWaldhausen (j ⁻¹ᵁ
      T).ι)) D)
    (n : ℕ) : Function.Injective (KMap (inclusion_exact j T) n) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := (flattenKEquiv j T h n).surjective x
  obtain ⟨b, rfl⟩ := (flattenKEquiv j T h n).surjective y
  apply congrArg (flattenKEquiv j T h n)
  apply h.inclusion_KMap_injective_general D hs n
  change ((KMap (inclusion_exact j T) n).comp (flattenKEquiv j T h n)) a =
    ((KMap (inclusion_exact j T) n).comp (flattenKEquiv j T h n)) b at hxy
  rwa [flattenKEquiv_inclusion] at hxy

/-- The inverse flattening comparison retains the same original inclusion homomorphism. -/
theorem flattenKEquiv_symm_inclusion (n : ℕ) :
    (KMap h.inclusion_exact n).comp (flattenKEquiv j T h n).symm.toMonoidHom =
      KMap (inclusion_exact j T) n := by
  ext x
  have hx := DFunLike.congr_fun (flattenKEquiv_inclusion j T h n) ((flattenKEquiv j T h n).symm x)
  exact hx.symm.trans (congrArg (KMap (inclusion_exact j T) n)
    ((flattenKEquiv j T h n).apply_symm_apply x))

/-- Flattening preserves the entire actual inclusion range in every degree. -/
theorem flatten_inclusion_range (n : ℕ) :
    (KMap (inclusion_exact j T) n).range = (KMap h.inclusion_exact n).range := by
  have hr : (flattenKEquiv j T h n :
      h.waldhausenStructure.K n →* (complexWaldhausen j T).K n).range = ⊤ :=
    MonoidHom.range_eq_top.mpr (flattenKEquiv j T h n).surjective
  rw [← flattenKEquiv_inclusion j T h n, MonoidHom.range_comp, hr, Subgroup.map_top]

end Quillen.PerfectComplexes.SupportedOpenDerivedImage

end

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace Quillen.PerfectComplexes.SupportedOpenDerivedImage
open Waldhausen Fibration
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens) [Fact
  (OpenDerivedImage.HasSupportedDerivedRoofs j T)]

/-- The two actual image functors factor the unchanged original relative restriction. -/
theorem relativeKMap_factor (n : ℕ) :
    (KMap (inclusion_exact j T) n).comp (KMap (relativeCorestrict_exact j T) n) =
      perfectSupportedOpenKRestrict j T n := by
  rw [Quillen.Waldhausen.KMap_comp_KMap]
  rfl

/-- The actual fine perfect cylinder supplies the cofinality data on any scheme. -/
def targetFineJointData (U : Scheme.{u}) (V : U.Opens) : RowFactorization.JointData (.refl
  (perfectSupportedWaldhausen V.ι)) :=
  complexJointDataOfNested (perfectSupported V.ι)
    (fun hK hL f => perfectSupported_mappingCone V.ι hK hL f)
    (fun _ hK => perfectSupported_shift V.ι hK 1) (.refl (perfectSupportedWaldhausen V.ι))

theorem targetFineJointData_section (U : Scheme.{u}) (V : U.Opens) :
    RowFactorization.SecondEndpointSection (.refl (perfectSupportedWaldhausen V.ι))
      (targetFineJointData U V) :=
  complexJointDataOfNested_secondEndpointSection (perfectSupported V.ι)
    (fun hK hL f => perfectSupported_mappingCone V.ι hK hL f)
    (fun _ hK => perfectSupported_shift V.ι hK 1) (.refl (perfectSupportedWaldhausen V.ι))

/-- The original relative restriction is bijective in positive degrees through
actual corestriction and genuine dense inclusion. -/
theorem relativeKRestrict_succ_bijective [HasBinaryCoproducts ((perfectSupported (j ⁻¹ᵁ
  T).ι).FullSubcategory)]
    (hd : Cofinality.DenseCofiberData (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι) (objects j T))
    (Jd : RowFactorization.JointData (.refl (weakArrowOpposite j T))) (n : ℕ) :
    Function.Bijective (perfectSupportedOpenKRestrict j T (n+1)) := by
  rw [← relativeKMap_factor j T (n+1)]
  exact (inclusion_KMap_succ_bijective j T hd (targetFineJointData U (j ⁻¹ᵁ T))
    (targetFineJointData_section U (j ⁻¹ᵁ T)) n).comp
    (relativeCorestrict_KMap_bijective j T Jd (n+1))

/-- The original relative restriction is injective also in degree zero. -/
theorem relativeKRestrict_injective [HasBinaryCoproducts ((perfectSupported (j ⁻¹ᵁ
  T).ι).FullSubcategory)]
    (hd : Cofinality.DenseCofiberData (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι) (objects j T))
    (Jd : RowFactorization.JointData (.refl (weakArrowOpposite j T))) (n : ℕ) :
    Function.Injective (perfectSupportedOpenKRestrict j T n) := by
  rw [← relativeKMap_factor j T n]
  exact (inclusion_KMap_injective j T hd (targetFineJointData U (j ⁻¹ᵁ T))
    (targetFineJointData_section U (j ⁻¹ᵁ T)) n).comp
    (relativeCorestrict_KMap_bijective j T Jd n).injective

end Quillen.PerfectComplexes.SupportedOpenDerivedImage

end
