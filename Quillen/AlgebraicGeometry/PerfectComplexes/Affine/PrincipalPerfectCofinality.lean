/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.OpenKEquivalence
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenComparisonNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PrincipalStrictCofinality
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenKZeroImage

/-!
# Original principal all-perfect relative K comparison

Over every commutative ring, the original principal relative-open perfect
restriction map is bijective in every positive connective degree and
injective in degree zero. The actual positive equivalence retains that
original restriction as its forward map. The degree-zero endpoint is
identified with precisely the existing subgroup `PerfectOpenKZeroImage`,
the image of original perfect restriction from the affine base.

The proof transports the genuine strict principal cofinality theorem through
the proved original relative and absolute affine strict/perfect comparisons,
using the literal original endpoint square. No comparison premise remains;
no full-target K₀ surjectivity is asserted. Arbitrary rings, zero divisors,
and localization at zero are included.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Quillen.PerfectComplexes.Affine
variable (R : CommRingCat.{u}) (r : R)

/-- Original principal-open perfect restriction is bijective in every
positive degree over arbitrary rings, including localization at zero. -/
lemma principal_perfectOpenKRestrict_succ_bijective (n : ℕ) :
    Function.Bijective (perfectOpenKRestrict (CoherentScheme.principalOpen R r) (n+1)) := by
  apply ((strictToPerfectOpenKMap_bijective R (CoherentScheme.principalOpen R r)
    (n+1)).of_comp_iff _).mp
  change Function.Bijective
    ((perfectOpenKRestrict (CoherentScheme.principalOpen R r) (n+1)).comp
      (strictToPerfectOpenKMap (CoherentScheme.principalOpen R r) (n+1)))
  rw [perfectOpenKRestrict_comp_strictToPerfectOpenKMap]
  exact (strictToPerfectKMap_bijective (.of (Localization.Away r)) (n+1)).comp
    (StrictOpenWeakImage.principal_relativeKRestrict_succ_bijective R r n)

/-- The original degree-zero principal perfect endpoint is injective.
Its honest target is the original restriction image, not all target K₀. -/
lemma principal_perfectOpenKRestrict_zero_injective :
    Function.Injective (perfectOpenKRestrict (CoherentScheme.principalOpen R r) 0) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := (strictToPerfectOpenKMap_bijective R (CoherentScheme.principalOpen R r)
    0).surjective x
  obtain ⟨b, rfl⟩ := (strictToPerfectOpenKMap_bijective R (CoherentScheme.principalOpen R r)
    0).surjective y
  apply congrArg (strictToPerfectOpenKMap (CoherentScheme.principalOpen R r) 0)
  apply StrictOpenWeakImage.principal_relativeKRestrict_zero_injective R r
  apply (strictToPerfectKMap_bijective (.of (Localization.Away r)) 0).injective
  change ((strictToPerfectKMap (Spec (.of (Localization.Away r))) 0).comp
    (StrictOpenWeakImage.relativeKRestrict (CoherentScheme.principalOpen R r) 0)) a =
    ((strictToPerfectKMap (Spec (.of (Localization.Away r))) 0).comp
    (StrictOpenWeakImage.relativeKRestrict (CoherentScheme.principalOpen R r) 0)) b
  rw [← perfectOpenKRestrict_comp_strictToPerfectOpenKMap]
  exact hxy

/-- Positive relative perfect K-theory agrees with target perfect K-theory
through the original relative restriction homomorphism. -/
def principalPerfectOpenKEquiv (n : ℕ) :
    PerfectOpenK (CoherentScheme.principalOpen R r) (n+1) ≃*
      PerfectK (Spec (.of (Localization.Away r))) (n+1) :=
  MulEquiv.ofBijective (perfectOpenKRestrict (CoherentScheme.principalOpen R r) (n+1))
    (principal_perfectOpenKRestrict_succ_bijective R r n)

/-- The monoid-hom coercion is the canonical forward map. -/
@[simp] lemma principalPerfectOpenKEquiv_coe (n : ℕ) :
    ↑(principalPerfectOpenKEquiv R r n) =
      perfectOpenKRestrict (CoherentScheme.principalOpen R r) (n+1) := rfl

/-- The degree-zero relative endpoint identifies with exactly the actual
image of original perfect restriction, without a target-surjectivity premise. -/
def principalPerfectOpenKZeroImageEquiv :
    PerfectOpenK (CoherentScheme.principalOpen R r) 0 ≃*
      PerfectOpenKZeroImage (CoherentScheme.principalOpen R r) :=
  MulEquiv.ofBijective (perfectOpenKZeroToImage (CoherentScheme.principalOpen R r))
    ⟨fun _ _ h => principal_perfectOpenKRestrict_zero_injective R r (congrArg Subtype.val h),
      perfectOpenKZeroToImage_surjective (CoherentScheme.principalOpen R r)⟩

@[simp] lemma principalPerfectOpenKZeroImageEquiv_coe
    (a : PerfectOpenK (CoherentScheme.principalOpen R r) 0) :
    (principalPerfectOpenKZeroImageEquiv R r a : PerfectK (Spec (.of (Localization.Away r))) 0) =
      perfectOpenKRestrict (CoherentScheme.principalOpen R r) 0 a := rfl

end Quillen.PerfectComplexes.Affine
