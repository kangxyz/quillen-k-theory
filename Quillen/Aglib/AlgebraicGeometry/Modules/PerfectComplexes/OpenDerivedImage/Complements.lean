/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.OpenDerivedImage.Closure
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Affine.PerfectComplement
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic

/-!
# Actual complements in the affine derived restriction image

On a compact open of an affine scheme, original locally perfect objects have the displayed strict complements. The chosen coproduct comparison retains the same actual chain complexes.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex



open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex TopologicalSpace
universe u
attribute [local instance] Scheme.Modules.standardHasDerivedCategory
namespace Quillen.PerfectComplexes.OpenDerivedImage
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

end Quillen.PerfectComplexes.OpenDerivedImage

end

end
