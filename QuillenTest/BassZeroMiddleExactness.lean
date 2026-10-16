/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.BassZeroMiddleExactness
public import Mathlib.Data.ZMod.Basic

/-! # Consumers of original affine Bass middle exactness

These tests recover a coefficient class from a compatible polynomial pair,
check its uniqueness, and exercise degrees zero and one, including the zero ring.
-/
@[expose] public section

set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true

open AlgebraicGeometry
open Quillen.PerfectComplexes Quillen.PerfectComplexes.ProjectiveLine.BassPositive

universe u

noncomputable section

namespace BassZeroMiddleExactnessConsumers

local instance (Y : Scheme.{u}) (n : ℕ) : CommGroup (PerfectK Y n) :=
  Quillen.Waldhausen.Additivity.KCommGroup (perfectWaldhausen Y) n

/-- The original degree-zero image and kernel agree. -/
theorem zero_exactness (R : CommRingCat.{u}) :
    (polynomialCoefficientPair R 0).range = (laurentDifference R 0).ker :=
  range_coefficientPair_zero_eq_ker_laurentDifference R

/-- A compatible polynomial pair has a unique original coefficient lift. -/
theorem unique_coefficient_lift (R : CommRingCat.{u})
    (x : PerfectK (Spec (.of (Polynomial R))) 0 × PerfectK (Spec (.of (Polynomial R))) 0)
    (hx : laurentDifference R 0 x = 1) :
    ∃! a : PerfectK (Spec R) 0, polynomialCoefficientPair R 0 a = x := by
  have hm : x ∈ (polynomialCoefficientPair R 0).range := by
    rw [range_coefficientPair_zero_eq_ker_laurentDifference]
    exact hx
  obtain ⟨a, ha⟩ := hm
  exact ⟨a, ha, fun b hb => polynomialCoefficientPair_injective R 0 (hb.trans ha.symm)⟩

/-- The all-degree interface includes its degree-zero boundary case. -/
theorem all_degrees_zero (R : CommRingCat.{u}) :
    (polynomialCoefficientPair R 0).range = (laurentDifference R 0).ker :=
  range_coefficientPair_eq_ker_laurentDifference_all R 0

/-- The all-degree interface retains positive-degree exactness. -/
theorem all_degrees_one (R : CommRingCat.{u}) :
    (polynomialCoefficientPair R 1).range = (laurentDifference R 1).ker :=
  range_coefficientPair_eq_ker_laurentDifference_all R 1

/-- No nontriviality assumption excludes the zero ring. -/
theorem zero_ring_exactness :
    (polynomialCoefficientPair (.of (ZMod 1)) 0).range =
      (laurentDifference (.of (ZMod 1)) 0).ker :=
  range_coefficientPair_zero_eq_ker_laurentDifference (.of (ZMod 1))

end BassZeroMiddleExactnessConsumers
