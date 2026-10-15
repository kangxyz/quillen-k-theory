/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionKZeroValue

/-! Every original coarse class lifts to a fine class with its unchanged original quotient value. -/
@[expose] public section

open Quillen.PerfectComplexes
open Quillen.Waldhausen

noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.AffineOpenPair
open Quillen.Waldhausen.AlgebraicGrothendieck
universe u
namespace QuillenTest.FullOpenSectionKZeroValue

open Quillen
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R)
  [IsOpenImmersion j] [CompactSpace U]

/-- A fine preimage retains both the same coarse class and its original raw quotient value. -/
theorem original_fine_preimage_with_value (a : Under R)
    (y : (boundedFlatAffineFullOpenSectionGrading j a).coarseStructure.K 0) :
    ∃ x : (boundedFlatAffineFullOpenSectionWaldhausen j a).K 0,
      KMap (Fibration.changeWeak_exact
        (boundedFlatAffineFullOpenSectionGrading j a).nested) 0 x = y ∧
      QuotientAddGroup.mk'
          (AlgebraicGrothendieck.map (perfectOpenWeakWaldhausen (inclusion j a))
            (perfectRestrict (inclusion j a))
            (perfectOpenRestrict_waldhausenExact (inclusion j a))).range
          ((grothendieckKZeroEquivOfSmallModel (perfectWaldhausen (openSpace j a))).symm
            (boundedFlatAffineFullOpenSectionPerfectKEquiv j a 0 x)).toAdd =
        (boundedFlatAffineFullOpenSectionKZeroValueMap j a y).toAdd := by
  obtain ⟨x, hx⟩ := boundedFlatAffineFullOpenSection_changeWeakKMap_zero_surjective j a y
  refine ⟨x, hx, ?_⟩
  have he := DFunLike.congr_fun
    (boundedFlatAffineFullOpenSectionKZeroValueMap_comp_changeWeak j a) x
  change boundedFlatAffineFullOpenSectionKZeroValueMap j a
      (KMap (Fibration.changeWeak_exact (boundedFlatAffineFullOpenSectionGrading j a).nested) 0 x) =
    (QuotientAddGroup.mk'
      (AlgebraicGrothendieck.map (perfectOpenWeakWaldhausen (inclusion j a))
        (perfectRestrict (inclusion j a))
        (perfectOpenRestrict_waldhausenExact (inclusion j a))).range).toMultiplicative
      ((grothendieckKZeroEquivOfSmallModel (perfectWaldhausen (openSpace j a))).symm
        (boundedFlatAffineFullOpenSectionPerfectKEquiv j a 0 x)) at he
  rw [hx] at he
  exact congrArg Multiplicative.toAdd he.symm

omit [CompactSpace U] in
/-- The actual original coarse value map reflects equality of every pair of graded classes. -/
theorem original_coarse_class_eq_iff (a : Under R)
    (x y : (boundedFlatAffineFullOpenSectionGrading j a).coarseStructure.K 0) :
    x = y ↔ boundedFlatAffineFullOpenSectionKZeroValueMap j a x =
      boundedFlatAffineFullOpenSectionKZeroValueMap j a y :=
  (boundedFlatAffineFullOpenSectionKZeroValueMap_injective j a).eq_iff.symm

end QuillenTest.FullOpenSectionKZeroValue
