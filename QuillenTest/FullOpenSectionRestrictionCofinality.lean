/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionRestrictionCofinality

/-!
# Class detection and unique lifting for the original section restriction

The actual restriction detects the unit K-zero class. Each positive-degree full-open
section class has a unique preimage under that same restriction. Compactness of the
initial open remains explicit.
-/
@[expose] public section

open Quillen.PerfectComplexes
open Quillen.Waldhausen

noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.AffineOpenPair
universe u
namespace QuillenTest.FullOpenSectionRestrictionCofinality

open Quillen
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R)
  [IsOpenImmersion j] [CompactSpace U]

/-- Original restriction detects whether a section K-zero class is the unit. -/
theorem restriction_K_zero_eq_one_iff (a : Under R)
    (x : (boundedFlatAffineSectionOpenWaldhausen (inclusion j a)).K 0) :
    KMap (boundedFlatAffineFullOpenSectionRestriction_exact j a) 0 x = 1 ↔ x = 1 := by
  let r := KMap (boundedFlatAffineFullOpenSectionRestriction_exact j a) 0
  change r x = 1 ↔ x = 1
  constructor
  · intro h
    apply boundedFlatAffineFullOpenSectionRestriction_KMap_zero_injective j a
    exact h.trans (map_one r).symm
  · rintro rfl
    exact map_one r

/-- Every positive full-open class lifts uniquely through the actual section restriction. -/
theorem existsUnique_restriction_K_succ_preimage (a : Under R) (n : ℕ)
    (y : (boundedFlatAffineFullOpenSectionWaldhausen j a).K (n + 1)) :
    ∃! x : (boundedFlatAffineSectionOpenWaldhausen (inclusion j a)).K (n + 1),
      KMap (boundedFlatAffineFullOpenSectionRestriction_exact j a) (n + 1) x = y := by
  have hr := boundedFlatAffineFullOpenSectionRestriction_KMap_succ_bijective j a n
  obtain ⟨x, hx⟩ := hr.surjective y
  refine ⟨x, hx, ?_⟩
  intro z hz
  exact hr.injective (hz.trans hx.symm)

end QuillenTest.FullOpenSectionRestrictionCofinality
