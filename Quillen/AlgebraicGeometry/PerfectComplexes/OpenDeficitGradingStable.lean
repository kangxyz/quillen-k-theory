/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDeficitGrading
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.KTheory
public import Quillen.Waldhausen.GrothendieckComparison.ImageQuotientConeZero
public import Quillen.Waldhausen.Cofinality.GeneralGraded

/-!
# The original deficit-to-grading map is a stable equivalence

The actual constructed cone map is identified on degree zero through the original K-map
image quotient. Under qcqs and quasi-compact-open hypotheses, both its original source and
its actual graded-coarse target vanish in every other signed degree. This is an objectwise
stable equivalence; no coefficient-natural or inherited Laurent seed square is asserted.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open Quillen.Waldhausen

noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS Quillen.Waldhausen.AlgebraicGrothendieck
universe u
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The actual fine cylinder proves concentration of the genuine graded-coarse target. -/
theorem perfectOpenDeficitGradedPrespectrum_stable_subsingleton (d : ℤ) (hd : d ≠ 0) :
    Subsingleton (stableHomotopyGroup (perfectOpenDeficitGradedPrespectrum j) d) := by
  by_cases hn : d < 0
  · exact originalStableHomotopyGroup_neg_subsingleton
      (perfectOpenDeficitGrading j).coarseStructure d hn
  · have he : d = (d.toNat : ℤ) := by omega
    have hp : d.toNat = (d.toNat - 1) + 1 := by omega
    let : Subsingleton ((perfectOpenDeficitGrading j).coarseStructure.K d.toNat) := by
      rw [hp]
      exact (perfectOpenDeficitGrading j).coarse_K_succ_subsingleton_general
        (OpenDerivedImage.targetFineJointData U) (d.toNat - 1)
    rw [he]
    let e := originalKStableEquiv (perfectOpenDeficitGrading j).coarseStructure d.toNat
    exact e.symm.injective.subsingleton

/-- The original unshifted cone descent is bijective in degree zero for every open immersion. -/
theorem perfectOpenDeficitGradingMap_stable_zero_bijective :
    Function.Bijective ((stableHomotopyFunctor 0).map (perfectOpenDeficitGradingMap j)) :=
  imageQuotientConeMap_stable_zero_bijective (perfectOpenWeakWaldhausen j) (perfectRestrict j)
    (perfectOpenRestrict_waldhausenExact j)
    (OpenDerivedImage.targetFineJointData U).reflexiveSmallModel.sourceFactorization

variable [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]

/-- The unchanged pointwise deficit comparison is a stable equivalence in all signed degrees. -/
theorem perfectOpenDeficitGradingMap_isStableEquivalence :
    IsStableEquivalence (perfectOpenDeficitGradingMap j) := by
  intro d
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  by_cases hd : d = 0
  · subst d
    exact perfectOpenDeficitGradingMap_stable_zero_bijective j
  · have hE := perfectOpenDeficit_stableHomotopyGroup_subsingleton j d hd
    have hG := perfectOpenDeficitGradedPrespectrum_stable_subsingleton j d hd
    exact ⟨fun _ _ _ => hE.elim _ _, fun _ => ⟨0, hG.elim _ _⟩⟩

end Quillen.PerfectComplexes
