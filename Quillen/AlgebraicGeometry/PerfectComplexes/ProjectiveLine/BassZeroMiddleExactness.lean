/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.BassPositiveFundamental
public import Quillen.AlgebraicGeometry.PerfectComplexes.MayerVietoris

/-! # Degree-zero middle exactness of the original affine Bass row

The connective degree-zero Mayer-Vietoris theorem, transported by the original
native chart and Laurent overlap equivalences, identifies the image of the
polynomial coefficient pair with the kernel of the signed Laurent difference.
Together with positive-degree exactness this gives middle exactness in every
natural degree, for every commutative ring, including the zero ring. No Laurent
section, negative-group comparison, or nonconnective localization is assumed.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry

namespace Quillen.PerfectComplexes.ProjectiveLine.BassPositive
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.ProjectiveLine FlasqueTwoSummands

attribute [local instance] Waldhausen.Additivity.KCommGroup

variable (R : CommRingCat.{u})

/-- The original chart and overlap squares transport genuine K-zero gluing
exactness to the literal polynomial pair and signed Laurent difference. -/
theorem affine_range_restrictionPair_zero_eq_ker_laurentDifference :
    (affineRestrictionPair R 0).range = (laurentDifference R 0).ker := by
  let j := affineNativeChart R false
  let T := positiveOpen R
  have h := PerfectMayerVietoris.qcqs_range_restrictionPair_zero_eq_ker_overlapDifference
    j T (positiveOpen_isCompact R) (affineNativeChart_cover R)
  have hr : Function.MulExact (PerfectMayerVietoris.restrictionPair j T 0)
      (PerfectMayerVietoris.overlapDifference j T 0) :=
    MonoidHom.mulExact_iff.mpr h.symm
  have hr' := (MonoidHom.mulExact_iff_of_surjective_of_bijective_of_injective
    (PerfectMayerVietoris.restrictionPair j T 0)
    (PerfectMayerVietoris.overlapDifference j T 0)
    (affineRestrictionPair R 0) (laurentDifference R 0)
    (MonoidHom.id _) (positivePairEquiv R 0).toMonoidHom
    (laurentOverlapEquiv R 0).toMonoidHom
    (by simpa only [MonoidHom.comp_id] using (affineRestrictionPair_square R 0).symm)
    (laurentDifference_square R 0).symm Function.surjective_id
    (positivePairEquiv R 0).bijective (laurentOverlapEquiv R 0).injective).mp hr
  exact (MonoidHom.mulExact_iff.mp hr').symm

/-- Middle exactness of the literal degree-zero polynomial coefficient row. -/
theorem range_coefficientPair_zero_eq_ker_laurentDifference :
    (polynomialCoefficientPair R 0).range = (laurentDifference R 0).ker := by
  rw [← affineRestrictionPair_range_eq_coefficientPair]
  exact affine_range_restrictionPair_zero_eq_ker_laurentDifference R

/-- Middle exactness of the original affine Bass row in every natural degree. -/
theorem range_coefficientPair_eq_ker_laurentDifference_all (n : ℕ) :
    (polynomialCoefficientPair R n).range = (laurentDifference R n).ker := by
  cases n with
  | zero => exact range_coefficientPair_zero_eq_ker_laurentDifference R
  | succ n => exact range_coefficientPair_eq_ker_laurentDifference R n

end Quillen.PerfectComplexes.ProjectiveLine.BassPositive
