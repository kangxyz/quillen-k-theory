/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionRestrictionKComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.GlobalCofinality

/-!
# Cofinality of the original full-open section restriction

The unchanged restriction K-map is injective in every degree and bijective in positive
degrees. Its actual evaluation square transports the installed perfect-complex cofinality
through the original section K-equivalences. Compactness of the initial open is retained;
no degree-zero surjectivity, literal Model-zero equality, or stable-equivalence input is used.
-/
@[expose] public section

open Quillen.Waldhausen

noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.AffineOpenPair
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R)
  [IsOpenImmersion j] [CompactSpace U]

/-- Actual evaluation transports injectivity to the unchanged original restriction K-map. -/
theorem boundedFlatAffineFullOpenSectionRestriction_KMap_injective (a : Under R) (n : ℕ) :
    Function.Injective (KMap (boundedFlatAffineFullOpenSectionRestriction_exact j a) n) := by
  let : CompactSpace (openSpace j a) := compactSpace_openSpace j a
  intro x y hxy
  apply (boundedFlatAffineSectionOpenPerfectKEquiv (inclusion j a) n).injective
  apply qcqs_perfectOpenKRestrict_injective (inclusion j a) n
  rw [← boundedFlatAffineFullOpenSectionRestriction_perfectKComparison j a n x,
    ← boundedFlatAffineFullOpenSectionRestriction_perfectKComparison j a n y, hxy]

/-- Original K-zero injectivity supplies the degree-one kernel term of the actual cone sequence. -/
theorem boundedFlatAffineFullOpenSectionRestriction_KMap_zero_injective (a : Under R) :
    Function.Injective (KMap (boundedFlatAffineFullOpenSectionRestriction_exact j a) 0) :=
  boundedFlatAffineFullOpenSectionRestriction_KMap_injective j a 0

/-- The same original restriction K-map is bijective in every strictly positive degree. -/
theorem boundedFlatAffineFullOpenSectionRestriction_KMap_succ_bijective
    (a : Under R) (n : ℕ) :
    Function.Bijective (KMap (boundedFlatAffineFullOpenSectionRestriction_exact j a) (n + 1)) := by
  let : CompactSpace (openSpace j a) := compactSpace_openSpace j a
  refine ⟨boundedFlatAffineFullOpenSectionRestriction_KMap_injective j a (n + 1), ?_⟩
  intro y
  obtain ⟨z, hz⟩ := (qcqs_perfectOpenKRestrict_succ_bijective (inclusion j a) n).surjective
    (boundedFlatAffineFullOpenSectionPerfectKEquiv j a (n + 1) y)
  refine ⟨(boundedFlatAffineSectionOpenPerfectKEquiv (inclusion j a) (n + 1)).symm z, ?_⟩
  apply (boundedFlatAffineFullOpenSectionPerfectKEquiv j a (n + 1)).injective
  rw [boundedFlatAffineFullOpenSectionRestriction_perfectKComparison,
    MulEquiv.apply_symm_apply]
  exact hz

end Quillen.PerfectComplexes
