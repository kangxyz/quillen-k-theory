/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionRestrictionKComparison

/-!
Original section restriction preimages correspond to original raw-perfect restriction preimages
in every degree. The comparison chooses witnesses through the actual evaluation equivalence
and does not assume either restriction map is surjective.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.PerfectComplexes AlgebraicGeometry.Scheme.AffineOpenPair Quillen.Waldhausen
universe u
namespace QuillenTest.FullOpenSectionRestrictionKComparison

open Quillen
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R)
  [IsOpenImmersion j] [CompactSpace U]

/-- A fine section class has an original restriction preimage exactly when its evaluation does. -/
theorem original_restriction_preimage_iff (a : Under R) (n : ℕ)
    (y : (boundedFlatAffineFullOpenSectionWaldhausen j a).K n) :
    (∃ x : (boundedFlatAffineSectionOpenWaldhausen (inclusion j a)).K n,
      KMap (boundedFlatAffineFullOpenSectionRestriction_exact j a) n x = y) ↔
      ∃ z : (perfectOpenWeakWaldhausen (inclusion j a)).K n,
        perfectOpenKRestrict (inclusion j a) n z =
          boundedFlatAffineFullOpenSectionPerfectKEquiv j a n y := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨boundedFlatAffineSectionOpenPerfectKEquiv (inclusion j a) n x,
      (boundedFlatAffineFullOpenSectionRestriction_perfectKComparison j a n x).symm⟩
  · rintro ⟨z, hz⟩
    obtain ⟨x, hx⟩ := (boundedFlatAffineSectionOpenPerfectKEquiv (inclusion j a) n).surjective z
    refine ⟨x, (boundedFlatAffineFullOpenSectionPerfectKEquiv j a n).injective ?_⟩
    rw [boundedFlatAffineFullOpenSectionRestriction_perfectKComparison, hx]
    exact hz

end QuillenTest.FullOpenSectionRestrictionKComparison
