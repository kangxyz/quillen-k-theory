/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PrincipalStrictCofinality

/-! # Actual principal strict cofinality and honest original K-zero image consumers -/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace QuillenTest.PrincipalStrictCofinality

open Quillen
open PerfectComplexes StrictOpenWeakImage Waldhausen
variable (R : CommRingCat.{u}) (r : R)

/-- Every strict target has an actual coproduct complement with an original weak restriction
  witness. -/
theorem actual_coproduct_complement
    [HasBinaryCoproducts (StrictPerfect (Spec (.of (Localization.Away r))))]
    (A : StrictPerfect (Spec (.of (Localization.Away r)))) :
    ∃ (B : StrictPerfect (Spec (.of (Localization.Away r)))) (E : StrictPerfect (Spec R))
      (p : (strictRestrict (CoherentScheme.principalOpen R r)).obj E ⟶ A ⨿ B),
      (strictWaldhausen _).weq p := principal_image_complement R r A

/-- Actual geometric cofinality gives unique preimages of every positive original strict K-class. -/
theorem unique_positive_original_preimage (n : ℕ) (b : StrictK (Spec (.of (Localization.Away r))) (n
  + 1)) :
    ∃! a, relativeKRestrict (CoherentScheme.principalOpen R r) (n + 1) a = b :=
  (principal_relativeKRestrict_succ_bijective R r n).existsUnique b

/-- The degree-zero original relative restriction is genuinely injective. -/
theorem original_relative_KZero_injective
    {a b : (coarseWaldhausen (CoherentScheme.principalOpen R r)).K 0}
    (h : relativeKRestrict (CoherentScheme.principalOpen R r) 0 a =
      relativeKRestrict (CoherentScheme.principalOpen R r) 0 b) : a = b :=
  principal_relativeKRestrict_zero_injective R r h

/-- Every actual extendible original K-zero class has exactly one relative representative. -/
theorem unique_extendible_KZero_preimage (b : KZeroImage (CoherentScheme.principalOpen R r)) :
    ∃! a, relativeKZeroToImage (CoherentScheme.principalOpen R r) a = b :=
  (principalRelativeKZeroImageEquiv R r).bijective.existsUnique b

/-- The honest image equivalence retains the original geometric restriction of every fine class. -/
theorem original_fine_KZero_restriction (a : StrictK (Spec R) 0) :
    (principalRelativeKZeroImageEquiv R r
      (KMap (Fibration.changeWeak_exact (nested (CoherentScheme.principalOpen R r))) 0 a) :
      StrictK (Spec (.of (Localization.Away r))) 0) = strictKRestrict (CoherentScheme.principalOpen
        R r) 0 a :=
  DFunLike.congr_fun (relativeKRestrict_comp_changeWeak (CoherentScheme.principalOpen R r) 0) a

/-- A genuinely nonextendible original K-zero class cannot be introduced by the relative model. -/
theorem nonextendible_KZero_has_no_relative_preimage
    (b : StrictK (Spec (.of (Localization.Away r))) 0)
    (hb : b ∉ (strictKRestrict (CoherentScheme.principalOpen R r) 0).range) :
    ¬ ∃ a, relativeKRestrict (CoherentScheme.principalOpen R r) 0 a = b := by
  intro h
  apply hb
  rw [← range_relativeKRestrict_zero (CoherentScheme.principalOpen R r)]
  exact h
end QuillenTest.PrincipalStrictCofinality
