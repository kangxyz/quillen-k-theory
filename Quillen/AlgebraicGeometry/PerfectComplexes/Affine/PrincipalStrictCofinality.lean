/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.StrictJointData
public import Quillen.AlgebraicGeometry.PerfectComplexes.StrictOpenKZeroImage
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PrincipalStrictDensity
public import Quillen.Waldhausen.Approximation.WeakImageCofinality

/-! # Original principal strict relative K-equivalences and the exact K-zero image

Genuine geometric restricted approximation and categorical cofinality prove
that original relative restriction is bijective in every positive degree and
injective at K-zero. Its actual K-zero target is precisely the original strict
restriction image. All constructions retain the original canonical maps.
Arbitrary locally-perfect/all-sheaf comparison is a separate step.
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

/-- Positive original principal relative restriction is bijective without a geometric lifting
  premise. -/
theorem principal_relativeKRestrict_succ_bijective (n : ℕ) :
    Function.Bijective (relativeKRestrict (CoherentScheme.principalOpen R r) (n + 1)) := by
  let : HasBinaryCoproducts (StrictPerfect (Spec (.of (Localization.Away r)))) :=
    Additivity.hasBinaryCoproducts (strictWaldhausen _)
  let : (strictWaldhausen (Spec (.of (Localization.Away r)))).weq.HasTwoOutOfThreeProperty :=
    inferInstanceAs (subcategoryWeakEquivalences (strictPerfect _)).HasTwoOutOfThreeProperty
  exact ApproximationImage.original_KMap_succ_bijective_of_dense
    (principal_approximationOnImage R r) (restriction_exact (CoherentScheme.principalOpen R r))
    (principalDenseData R r) (coarseJointData (CoherentScheme.principalOpen R r))
    (fineJointData _) (fineJointData_section _) n

/-- Degree-zero original relative restriction is injective; full-target surjectivity is not claimed.
-/
theorem principal_relativeKRestrict_zero_injective :
    Function.Injective (relativeKRestrict (CoherentScheme.principalOpen R r) 0) := by
  let : HasBinaryCoproducts (StrictPerfect (Spec (.of (Localization.Away r)))) :=
    Additivity.hasBinaryCoproducts (strictWaldhausen _)
  let : (strictWaldhausen (Spec (.of (Localization.Away r)))).weq.HasTwoOutOfThreeProperty :=
    inferInstanceAs (subcategoryWeakEquivalences (strictPerfect _)).HasTwoOutOfThreeProperty
  exact ApproximationImage.original_KMap_injective_of_dense
    (principal_approximationOnImage R r) (restriction_exact (CoherentScheme.principalOpen R r))
    (principalDenseData R r) (coarseJointData (CoherentScheme.principalOpen R r))
    (fineJointData _) (fineJointData_section _) 0

/-- The unchanged principal relative restriction itself supplies every positive K-equivalence. -/
def principalRelativeKEquiv (n : ℕ) : (coarseWaldhausen (CoherentScheme.principalOpen R r)).K (n +
  1) ≃*
    StrictK (Spec (.of (Localization.Away r))) (n + 1) :=
  MulEquiv.ofBijective (relativeKRestrict (CoherentScheme.principalOpen R r) (n + 1))
    (principal_relativeKRestrict_succ_bijective R r n)

/-- Principal relative K-zero identifies with the honest image of original strict restriction. -/
def principalRelativeKZeroImageEquiv : (coarseWaldhausen (CoherentScheme.principalOpen R r)).K 0 ≃*
    KZeroImage (CoherentScheme.principalOpen R r) :=
  MulEquiv.ofBijective (relativeKZeroToImage (CoherentScheme.principalOpen R r))
    ⟨fun _ _ h ↦ principal_relativeKRestrict_zero_injective R r (congrArg Subtype.val h),
      relativeKZeroToImage_surjective (CoherentScheme.principalOpen R r)⟩

/-- The K-zero image equivalence retains the original actual restriction homomorphism. -/
@[simp] theorem principalRelativeKZeroImageEquiv_coe
    (a : (coarseWaldhausen (CoherentScheme.principalOpen R r)).K 0) :
    (principalRelativeKZeroImageEquiv R r a : StrictK (Spec (.of (Localization.Away r))) 0) =
      relativeKRestrict (CoherentScheme.principalOpen R r) 0 a := rfl

end Quillen.PerfectComplexes.StrictOpenWeakImage
