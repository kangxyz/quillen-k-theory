/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionRestrictionExact
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionKComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionOpenKComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.PairRestriction

/-!
# Original section restriction on K-groups

The literal restriction/evaluation equality is lifted through the same `AsSmall` functors
as the original section K-equivalences. Actual small-model naturality and composition of
canonical K-maps then identify the original restriction in every degree. The final perfect
comparison retains the installed bounded-flat inclusion/restriction square. Compactness is
needed only for the full-open perfect comparison, not for the bounded-flat square.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen Quillen.Scheme.AffineOpenPair
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The actual evaluation square uses exactly the existing common-universe lifts. -/
theorem boundedFlatAffineFullOpenSectionRestriction_comp_smallEvaluation (a : Under R) :
    boundedFlatAffineFullOpenSectionRestriction j a ⋙
        (boundedFlatAffineFullOpenSectionSmallEquivalence j a).functor =
      (boundedFlatAffineSectionSmallEquivalence a.right).functor ⋙
        smallModelFunctor (boundedFlatPerfectPullback (inclusion j a)) := by
  change (boundedFlatAffineFullOpenSectionRestriction j a ⋙
      boundedFlatAffineFullOpenOriginalEvaluation j a) ⋙ AsSmall.up =
    (boundedFlatAffineOriginalEvaluation a.right ⋙ AsSmall.up) ⋙
      (AsSmall.down ⋙ boundedFlatPerfectPullback (inclusion j a) ⋙ AsSmall.up)
  rw [boundedFlatAffineFullOpenSectionRestriction_comp_evaluation]
  rfl

/-- Original bounded-flat evaluation K-equivalences commute with the exact section restriction. -/
theorem boundedFlatAffineFullOpenSectionRestriction_KComparison (a : Under R) (n : ℕ)
    (x : (boundedFlatAffineSectionOpenWaldhausen (inclusion j a)).K n) :
    boundedFlatAffineFullOpenSectionKEquiv j a n
        (KMap (boundedFlatAffineFullOpenSectionRestriction_exact j a) n x) =
      boundedFlatPerfectOpenKRestrict (inclusion j a) n
        (boundedFlatAffineSectionOpenKEquiv (inclusion j a) n x) := by
  have hs :
      (KMap (boundedFlatAffineFullOpenSectionSmallEquivalence_exact j a) n).comp
          (KMap (boundedFlatAffineFullOpenSectionRestriction_exact j a) n) =
        (KMap (boundedFlatPerfectOpenRestriction_exact (inclusion j a)).smallModel n).comp
          (KMap (boundedFlatAffineSectionOpenSmallEquivalence_exact (inclusion j a)) n) := by
    rw [KMap_comp_KMap, KMap_comp_KMap]
    exact KMap_eq_of_iso _ _
      (eqToIso (boundedFlatAffineFullOpenSectionRestriction_comp_smallEvaluation j a)) n
  apply ((boundedFlatPerfectWaldhausen (openSpace j a)).smallModelKEquiv n).injective
  have hn := DFunLike.congr_fun
    (smallModelKEquiv_naturality (boundedFlatPerfectOpenRestriction_exact (inclusion j a)) n)
    (boundedFlatAffineSectionOpenKEquiv (inclusion j a) n x)
  change (boundedFlatPerfectWaldhausen (openSpace j a)).smallModelKEquiv n
      (KMap (boundedFlatPerfectOpenRestriction_exact (inclusion j a)) n
        (boundedFlatAffineSectionOpenKEquiv (inclusion j a) n x)) =
    KMap (boundedFlatPerfectOpenRestriction_exact (inclusion j a)).smallModel n
      ((boundedFlatPerfectOpenWaldhausen (inclusion j a)).smallModelKEquiv n
        (boundedFlatAffineSectionOpenKEquiv (inclusion j a) n x)) at hn
  have hc : (boundedFlatPerfectOpenWaldhausen (inclusion j a)).smallModelKEquiv n
      (boundedFlatAffineSectionOpenKEquiv (inclusion j a) n x) =
    KMap (boundedFlatAffineSectionOpenSmallEquivalence_exact (inclusion j a)) n x := by
    rw [boundedFlatAffineSectionOpenKEquiv_apply, MulEquiv.apply_symm_apply]
  rw [hc] at hn
  rw [boundedFlatAffineFullOpenSectionKEquiv_apply, MulEquiv.apply_symm_apply]
  change KMap (boundedFlatAffineFullOpenSectionSmallEquivalence_exact j a) n
      (KMap (boundedFlatAffineFullOpenSectionRestriction_exact j a) n x) =
    (boundedFlatPerfectWaldhausen (openSpace j a)).smallModelKEquiv n
      (KMap (boundedFlatPerfectOpenRestriction_exact (inclusion j a)) n
        (boundedFlatAffineSectionOpenKEquiv (inclusion j a) n x))
  rw [hn]
  exact DFunLike.congr_fun hs x

variable [CompactSpace U]

/-- The actual restriction is the original perfect relative-open restriction in every degree. -/
theorem boundedFlatAffineFullOpenSectionRestriction_perfectKComparison
    (a : Under R) (n : ℕ)
    (x : (boundedFlatAffineSectionOpenWaldhausen (inclusion j a)).K n) :
    boundedFlatAffineFullOpenSectionPerfectKEquiv j a n
        (KMap (boundedFlatAffineFullOpenSectionRestriction_exact j a) n x) =
      perfectOpenKRestrict (inclusion j a) n
        (boundedFlatAffineSectionOpenPerfectKEquiv (inclusion j a) n x) := by
  rw [boundedFlatAffineFullOpenSectionPerfectKEquiv_apply,
    boundedFlatAffineFullOpenSectionRestriction_KComparison,
    boundedFlatAffineSectionOpenPerfectKEquiv_apply]
  exact (DFunLike.congr_fun
    (boundedFlatPerfectOpenKRestrict_comparison (inclusion j a) n)
    (boundedFlatAffineSectionOpenKEquiv (inclusion j a) n x)).symm

end Quillen.PerfectComplexes
