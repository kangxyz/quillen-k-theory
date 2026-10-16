/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenComparison
public import Quillen.Waldhausen.WeakArrow.RelativeKEquivalence
public import Quillen.Waldhausen.Approximation.DualInverseImage
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.StrictPerfectKEquivalence

/-! # Genuine affine relative-open strict-to-perfect approximation

Every original open of an affine base is permitted. The target open need not
be affine or quasi-compact. The original fine weak-arrow objects and incoming
factorizations supply the relative comparison via inverse-image duality.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open Quillen.Waldhausen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes.Affine

/-- The actual relative-open comparison is bijective in every degree over an affine base. -/
theorem strictToPerfectOpenKMap_bijective (R : CommRingCat.{u})
    {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j] (n : ℕ) :
    Function.Bijective (strictToPerfectOpenKMap j n) := by
  let : (perfectWaldhausen U).weq.HasTwoOutOfThreeProperty :=
    complexSubcategory_saturated (locallyPerfect U)
  apply (WeakArrow.Relative.KMap_bijective_iff_target.{u+1,u}
    (strictWaldhausen (Spec R)) (perfectWaldhausen (Spec R)) (perfectWaldhausen U)
    (strictToPerfect (Spec R)) (perfectRestrict j)
    (strictToPerfectExact (Spec R)) (perfectRestrict_waldhausenExact j) n).mpr
  exact KMap_bijective_of_dualApproximation_inverseImage
    (WeakArrow.dual_compatible (strictWaldhausen (Spec R)) (perfectWaldhausen (Spec R))
      (strictOppositeWaldhausen (Spec R)) (perfectOppositeWaldhausen (Spec R))
      (strictToPerfect (Spec R)) (strictToPerfectExact (Spec R)) (strictToPerfect_op_exact (Spec R))
      (perfectOppositeWaldhausen_compatible (Spec R)) (strictOppositeWaldhausen_compatible (Spec
        R)))
    (perfectOppositeWaldhausen_compatible (Spec R))
    (perfectOppositeWaldhausen_compatible U)
    (WeakArrow.target_exact (strictWaldhausen (Spec R)) (perfectWaldhausen (Spec R))
      (strictToPerfect (Spec R)) (strictToPerfectExact (Spec R)))
    (WeakArrow.dual_target_exact (strictWaldhausen (Spec R)) (perfectWaldhausen (Spec R))
      (strictOppositeWaldhausen (Spec R)) (perfectOppositeWaldhausen (Spec R))
      (strictToPerfect (Spec R)) (strictToPerfectExact (Spec R)) (strictToPerfect_op_exact (Spec R))
      (perfectOppositeWaldhausen_compatible (Spec R)))
    (perfectRestrict_waldhausenExact j) (perfectRestrict_op_exact j)
    (strictToPerfect_target_hasDualApproximation R) (strictToPerfectWeakArrowJointData (Spec R)) n

/-- Relative-open affine comparison with precisely the original forward K-map. -/
def strictToPerfectOpenKEquiv (R : CommRingCat.{u})
    {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j] (n : ℕ) :
    (StrictOpenWeakImage.coarseWaldhausen j).K n ≃* PerfectOpenK j n :=
  MulEquiv.ofBijective (strictToPerfectOpenKMap j n) (strictToPerfectOpenKMap_bijective R j n)

/-- The monoid-hom coercion is the canonical forward map. -/
@[simp] theorem strictToPerfectOpenKEquiv_coe (R : CommRingCat.{u})
    {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j] (n : ℕ) :
    ↑(strictToPerfectOpenKEquiv R j n) = strictToPerfectOpenKMap j n := rfl

end Quillen.PerfectComplexes.Affine
