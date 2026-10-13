/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionKZeroExact

/-! Original fine classes have the same coarse class exactly up to actual section restriction. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.PerfectComplexes Quillen.Scheme.AffineOpenPair Quillen.Waldhausen
universe u
namespace QuillenTest.FullOpenSectionKZeroExact

open Quillen
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R)
  [IsOpenImmersion j] [CompactSpace U]

/-- Equality after original changeWeak means precisely multiplication by a restricted class. -/
theorem coarse_eq_iff_restriction_multiple (a : Under R)
    (x y : (boundedFlatAffineFullOpenSectionWaldhausen j a).K 0) :
    (∃ w : (boundedFlatAffineSectionOpenWaldhausen (inclusion j a)).K 0,
      KMap (boundedFlatAffineFullOpenSectionRestriction_exact j a) 0 w * y = x) ↔
      KMap (Fibration.changeWeak_exact (boundedFlatAffineFullOpenSectionGrading j a).nested) 0 x =
        KMap (Fibration.changeWeak_exact
          (boundedFlatAffineFullOpenSectionGrading j a).nested) 0 y := by
  let r := KMap (boundedFlatAffineFullOpenSectionRestriction_exact j a) 0
  let g := KMap (Fibration.changeWeak_exact (boundedFlatAffineFullOpenSectionGrading j a).nested) 0
  have hr : r.range = g.ker :=
    boundedFlatAffineFullOpenSection_changeWeakKMap_zero_range_ker j a
  change (∃ w, r w * y = x) ↔ g x = g y
  constructor
  · rintro ⟨w, rfl⟩
    have hw : r w ∈ g.ker := by
      rw [← hr]
      exact ⟨w, rfl⟩
    change g (r w) = 1 at hw
    rw [map_mul, hw, one_mul]
  · intro h
    have hxy : x * y⁻¹ ∈ g.ker := by
      change g (x * y⁻¹) = 1
      rw [map_mul, map_inv, h, mul_inv_cancel]
    rw [← hr] at hxy
    obtain ⟨w, hw⟩ := hxy
    exact ⟨w, by rw [hw, mul_assoc, inv_mul_cancel, mul_one]⟩

end QuillenTest.FullOpenSectionKZeroExact
