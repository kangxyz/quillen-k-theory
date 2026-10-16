/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.Closure
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PerfectComplement
public import Quillen.CategoryTheory.Abelian.ZeroPushout
public import Quillen.Waldhausen.Cofinality.GeneralDense
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
/-! # Original dense cofiber data for the derived-saturated open image -/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open Quillen.Waldhausen


open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex TopologicalSpace
universe u
attribute [local instance] Scheme.Modules.standardHasDerivedCategory
namespace Quillen.PerfectComplexes.OpenDerivedImage
open Waldhausen
attribute [local instance] HasDerivedCategory.standard Abelian.hasFiniteBiproducts
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The genuine explicit complement theorem gives density in the original
DERIVED-saturated target, even for arbitrary all-sheaf terms of E. -/
theorem exists_strict_complement (R : CommRingCat.{u})
    (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    (E : CochainComplex W.toScheme.Modules ℤ) (hE : locallyPerfect W.toScheme E) :
    ∃ C : CochainComplex W.toScheme.Modules ℤ, strictPerfect W.toScheme C ∧ complexObjects W.ι
      (C ⊞ E) := by
  obtain ⟨K, P, n, hP, f, eK, _, _, hC, _, e, _⟩ :=
    Affine.locallyPerfect_exists_actual_perfect_complement R W hW E hE 0
  exact ⟨_, hC, (Affine.associatedComplex R).obj P,
    locallyPerfect_of_strictPerfect (Affine.strictPerfect_associated R hP), ⟨e⟩⟩

/-- The actual chosen perfect zero belongs to the original saturated image. -/
theorem zero_mem : objects j (perfectWaldhausen U).zero :=
  of_weakImage j (ApproximationImage.zero_mem (perfectRestrict_waldhausenExact j))

/-- Genuine cofibration pushouts yield original short exact sequences and
hence extension membership in the unchanged chain category. -/
theorem extension_mem (hroof : HasDerivedRoofs j)
    {A B Q : Perfect U} {i : A ⟶ B} {q : B ⟶ Q}
    (hi : (perfectWaldhausen U).cof i)
    (h : IsPushout i ((perfectWaldhausen U).isZero.from_ A) q
      ((perfectWaldhausen U).isZero.to_ Q))
    (hA : objects j A) (hQ : objects j Q) : objects j B := by
  have hp := (complexSubcategory_inclusion_exact (locallyPerfect U)).pushout hi h
  have : Mono ((locallyPerfect U).ι.map i) :=
    (complexSubcategory_inclusion_exact (locallyPerfect U)).cofibration i hi
  obtain ⟨z, hz⟩ := Quillen.Abelian.shortExact_of_mono_pushout_zero
    ((locallyPerfect U).ι.map_isZero (perfectWaldhausen U).isZero) hp
  exact complexObjects_of_shortExact j hroof hz hA hQ

/-- The original cofiber is retained in the quotient closure statement. -/
theorem quotient_mem (hroof : HasDerivedRoofs j)
    {A B Q : Perfect U} {i : A ⟶ B} {q : B ⟶ Q}
    (hi : (perfectWaldhausen U).cof i)
    (h : IsPushout i ((perfectWaldhausen U).isZero.from_ A) q
      ((perfectWaldhausen U).isZero.to_ Q))
    (hA : objects j A) (hB : objects j B) : objects j Q := by
  have hp := (complexSubcategory_inclusion_exact (locallyPerfect U)).pushout hi h
  have : Mono ((locallyPerfect U).ι.map i) :=
    (complexSubcategory_inclusion_exact (locallyPerfect U)).cofibration i hi
  obtain ⟨z, hz⟩ := Quillen.Abelian.shortExact_of_mono_pushout_zero
    ((locallyPerfect U).ι.map_isZero (perfectWaldhausen U).isZero) hp
  exact complexObjects_quotient_of_shortExact j hroof hz hA hB

/-- Actual complex complements give membership of the original chosen
categorical coproduct through its genuine colimit comparison. -/
theorem coprod_complement_of_complex_complement [HasBinaryCoproducts (Perfect U)]
    (A : Perfect U) (C : CochainComplex U.Modules ℤ) (hC : locallyPerfect U C)
    (hAC : complexObjects j (C ⊞ A.obj)) :
    ∃ B : Perfect U, objects j (A ⨿ B) := by
  let B : Perfect U := ⟨C, hC⟩
  let T : Perfect U := ⟨A.obj ⊞ B.obj,
    (abelianExactStructure _).prop_biprod _ A.property B.property⟩
  let il : A ⟶ T := ObjectProperty.homMk biprod.inl
  let ir : B ⟶ T := ObjectProperty.homMk biprod.inr
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
  let e : A ⨿ B ≅ T := (coprodIsCoprod A B).coconePointUniqueUpToIso ht
  have hT : complexObjects j T.obj := (complexObjects_iff_of_derivedIso j
    ((DerivedCategory.Q (C := U.Modules)).mapIso (biprod.braiding A.obj C))).mpr hAC
  exact ⟨B, (complexObjects_iff_of_derivedIso j
    ((DerivedCategory.Q (C := U.Modules)).mapIso ((locallyPerfect U).ι.mapIso e))).mpr hT⟩

/-- Genuine geometric complements provide actual original coproduct density
on every compact open of an affine scheme. -/
theorem affine_complement (R : CommRingCat.{u}) (W : (Spec R).Opens)
    (hW : IsCompact (W : Set (Spec R))) [HasBinaryCoproducts (Perfect W.toScheme)]
    (A : Perfect W.toScheme) : ∃ B : Perfect W.toScheme, objects W.ι (A ⨿ B) := by
  obtain ⟨C, hC, hAC⟩ := exists_strict_complement R W hW A.obj A.property
  exact coprod_complement_of_complex_complement W.ι A C (locallyPerfect_of_strictPerfect hC) hAC

/-- All genuine cofinality inputs reduce precisely to the displayed actual
open-derived roof property. Density itself has no further geometric premise. -/
theorem affineDenseData (R : CommRingCat.{u}) (W : (Spec R).Opens)
    (hW : IsCompact (W : Set (Spec R))) (hroof : HasDerivedRoofs W.ι)
    [HasBinaryCoproducts (Perfect W.toScheme)] :
    Cofinality.DenseCofiberData (perfectWaldhausen W.toScheme) (objects W.ι) where
  zero := zero_mem W.ι
  weak f hf := by
    have : QuasiIso f.hom := hf
    exact complexObjects_iff_of_quasiIso W.ι f.hom
  extension := extension_mem W.ι hroof
  quotient := quotient_mem W.ι hroof
  complement := affine_complement R W hW

end Quillen.PerfectComplexes.OpenDerivedImage
