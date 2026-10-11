/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionPrespectrum
public import Quillen.Waldhausen.Functoriality.ExactEquivalence

/-!
# Actual section evaluation and the original bounded-flat model

Section morphisms live in universe `u+1`, whereas original bounded-flat morphisms live in `u`.
The actual evaluation equivalence followed by the existing `AsSmall` equivalence gives a common
universe comparison. Its exact functors produce the genuine original all-degree K-equivalence.
The prespectrum comparison is the original zero-preserving model map of this same functor.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes

/-- The actual evaluation equivalence followed by the existing original common-universe model. -/
def boundedFlatAffineSectionSmallEquivalence (R : CommRingCat.{u}) :
    BoundedFlatAffineSections R ≌ SmallModel (BoundedFlatPerfect (Spec R)) :=
  (boundedFlatAffineSectionEquivalence R).trans AsSmall.equiv

/-- The original forward evaluation followed by actual universe lifting is exact. -/
theorem boundedFlatAffineSectionSmallEquivalence_exact (R : CommRingCat.{u}) :
    IsExact (boundedFlatAffineSectionWaldhausen R).cof
      (boundedFlatAffineSectionWaldhausen R).weq
      (boundedFlatPerfectWaldhausen (Spec R)).smallModel.cof
      (boundedFlatPerfectWaldhausen (Spec R)).smallModel.weq
      (boundedFlatAffineSectionSmallEquivalence R).functor :=
  (boundedFlatAffineOriginalEvaluation_exact R).comp
    (boundedFlatPerfectWaldhausen (Spec R)).smallModel_up_exact

/-- The actual inverse, original universe lowering followed by evaluation inverse, is exact. -/
theorem boundedFlatAffineSectionSmallEquivalence_inverse_exact (R : CommRingCat.{u}) :
    IsExact (boundedFlatPerfectWaldhausen (Spec R)).smallModel.cof
      (boundedFlatPerfectWaldhausen (Spec R)).smallModel.weq
      (boundedFlatAffineSectionWaldhausen R).cof (boundedFlatAffineSectionWaldhausen R).weq
      (boundedFlatAffineSectionSmallEquivalence R).inverse :=
  (boundedFlatPerfectWaldhausen (Spec R)).smallModel_down_exact.comp
    (boundedFlatAffineSectionEquivalence_inverse_exact R)

/-- A genuine all-degree equivalence with the unchanged original bounded-flat K-groups. -/
def boundedFlatAffineSectionKEquiv (R : CommRingCat.{u}) (n : ℕ) :
    (boundedFlatAffineSectionWaldhausen R).K n ≃*
      (boundedFlatPerfectWaldhausen (Spec R)).K n :=
  (KEquivOfExactEquivalence (boundedFlatAffineSectionWaldhausen R)
    (boundedFlatPerfectWaldhausen (Spec R)).smallModel
    (boundedFlatAffineSectionSmallEquivalence R)
    (boundedFlatAffineSectionSmallEquivalence_exact R)
    (boundedFlatAffineSectionSmallEquivalence_inverse_exact R) n).trans
      ((boundedFlatPerfectWaldhausen (Spec R)).smallModelKEquiv n).symm

/-- The comparison retains the actual forward exact-functor K-map before original universe lowering.
-/
theorem boundedFlatAffineSectionKEquiv_apply (R : CommRingCat.{u}) (n : ℕ)
    (a : (boundedFlatAffineSectionWaldhausen R).K n) :
    boundedFlatAffineSectionKEquiv R n a =
      ((boundedFlatPerfectWaldhausen (Spec R)).smallModelKEquiv n).symm
        (KMap (boundedFlatAffineSectionSmallEquivalence_exact R) n a) := rfl

/-- Original evaluation supplies an actual zero-preserving map into the original small model. -/
def boundedFlatAffineSectionEvaluationModelMap (R : CommRingCat.{u}) :
    boundedFlatAffineSectionModel R ⟶ modelOf (boundedFlatPerfectWaldhausen (Spec R)) where
  functor := (boundedFlatAffineSectionSmallEquivalence R).functor
  exact := boundedFlatAffineSectionSmallEquivalence_exact R
  zero := by
    change AsSmall.up.obj ((boundedFlatAffineOriginalEvaluation R).obj
        (boundedFlatAffineSectionWaldhausen R).zero) =
      AsSmall.up.obj (boundedFlatPerfectWaldhausen (Spec R)).zero
    rw [boundedFlatAffineSectionWaldhausen_zero, boundedFlatAffineOriginalEvaluation_sectionZero]

/-- The same original evaluation functor gives an actual comparison of original prespectra. -/
def boundedFlatAffineSectionEvaluationPrespectrumMap (R : CommRingCat.{u}) :
    boundedFlatAffineSectionPrespectrumFunctor.obj R ⟶
      originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R)) :=
  prespectrumMap (boundedFlatAffineSectionEvaluationModelMap R)

/-- The model comparison retains actual evaluation followed by original universe lifting. -/
theorem boundedFlatAffineSectionEvaluationModelMap_functor (R : CommRingCat.{u}) :
    (boundedFlatAffineSectionEvaluationModelMap R).functor =
      boundedFlatAffineOriginalEvaluation R ⋙ AsSmall.up := rfl

/-- The actual prespectrum comparison induces the proved unchanged original K-equivalence. -/
theorem boundedFlatAffineSectionEvaluationPrespectrumMap_zeroSpace (R : CommRingCat.{u})
    (n : ℕ) (a : (boundedFlatAffineSectionWaldhausen R).K n) :
    originalZeroSpaceEquiv (boundedFlatPerfectWaldhausen (Spec R)) n
        (boundedFlatAffineSectionKEquiv R n a) =
      homotopyGroupMap ((boundedFlatAffineSectionEvaluationPrespectrumMap R).map 0)
        ((boundedFlatAffineSectionEvaluationPrespectrumMap R).map_point 0)
        (boundedFlatAffineSectionZeroSpaceEquiv R n a) := by
  change zeroSpaceHomotopyEquiv (modelOf (boundedFlatPerfectWaldhausen (Spec R))) n
      ((boundedFlatPerfectWaldhausen (Spec R)).smallModelKEquiv n
        (boundedFlatAffineSectionKEquiv R n a)) = _
  rw [boundedFlatAffineSectionKEquiv_apply, MulEquiv.apply_symm_apply]
  rw [KMap_eq_piMap_of_zeroEq (boundedFlatAffineSectionSmallEquivalence_exact R)
    (boundedFlatAffineSectionEvaluationModelMap R).zero]
  exact loopShiftEquiv_natural n
    (deloopingMap (boundedFlatAffineSectionSmallEquivalence_exact R)).hom
    (stageMap_point 0 (boundedFlatAffineSectionEvaluationModelMap R)) a

end Quillen.PerfectComplexes
