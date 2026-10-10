/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PrincipalImageExtensions
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PrincipalStrictWeakImage
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PrincipalProjectiveExtension
public import Quillen.Waldhausen.Cofinality.DenseSubcategory

/-! # Genuine density and cofiber closure of the principal strict witnessed image

Actual geometric weak repleteness and extension closure, the previously
proved original pushout closure, and actual shifted extension establish all
categorical density data. Complement membership retains an actual original
restriction-to-target weak map, with the actual coproduct comparison.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes.StrictOpenWeakImage
open Waldhausen Fibration

variable (R : CommRingCat.{u}) (r : R)
  [HasBinaryCoproducts (StrictPerfect (Spec (.of (Localization.Away r))))]

/-- The original shifted complex is an actual coproduct complement in the witnessed strict image. -/
theorem principal_image_complement (A : StrictPerfect (Spec (.of (Localization.Away r)))) :
    ∃ B : StrictPerfect (Spec (.of (Localization.Away r))),
      ApproximationImage.objects (strictWaldhausen _) (strictRestrict (CoherentScheme.principalOpen
        R r)) (A ⨿ B) := by
  let B : StrictPerfect (Spec (.of (Localization.Away r))) := ⟨A.obj⟦(1 : ℤ)⟧, strictPerfect_shift
    A.property 1⟩
  let T : StrictPerfect (Spec (.of (Localization.Away r))) :=
    ⟨A.obj ⊞ B.obj, (abelianExactStructure _).prop_biprod _ A.property B.property⟩
  let il : A ⟶ T := ObjectProperty.homMk biprod.inl
  let ir : B ⟶ T := ObjectProperty.homMk biprod.inr
  have ht : IsColimit (BinaryCofan.mk il ir) := by
    refine BinaryCofan.IsColimit.mk _ (fun f g ↦ ObjectProperty.homMk (biprod.desc f.hom g.hom)) ?_
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
      · exact (congrArg (fun k ↦ k.hom) hm).trans (biprod.inl_desc _ _).symm
      · exact (congrArg (fun k ↦ k.hom) hn).trans (biprod.inr_desc _ _).symm
  let e : A ⨿ B ≅ T := (coprodIsCoprod A B).coconePointUniqueUpToIso ht
  obtain ⟨Q, ⟨q⟩⟩ := Affine.exists_principal_strict_extension_after_shift R r A
  let p : (strictRestrict (CoherentScheme.principalOpen R r)).obj Q ⟶ T := ObjectProperty.homMk
    q.hom
  exact ⟨B, Q, p ≫ e.inv, (strictWaldhausen _).weq.comp_mem _ _ q.quasiIso_hom
    ((strictWaldhausen _).weq_iso _ inferInstance)⟩

/-- Every density and cofiber condition is proved for the literal original strict restriction image.
-/
theorem principalDenseData : Cofinality.DenseCofiberData (strictWaldhausen _)
    (ApproximationImage.objects (strictWaldhausen _) (strictRestrict (CoherentScheme.principalOpen R
      r))) where
  zero := ApproximationImage.zero_mem (restriction_exact (CoherentScheme.principalOpen R r))
  weak f hf := Affine.principal_strict_image_iff_of_weak R r f hf
  extension hi h hA hQ := Affine.principal_strict_image_extension R r hi h hA hQ
  quotient hi h hA hB := ApproximationImage.pushout_mem (principal_approximationOnImage R r)
    (restriction_exact (CoherentScheme.principalOpen R r)) hi h hA hB
    (ApproximationImage.zero_mem (restriction_exact (CoherentScheme.principalOpen R r)))
  complement := principal_image_complement R r

end Quillen.PerfectComplexes.StrictOpenWeakImage
