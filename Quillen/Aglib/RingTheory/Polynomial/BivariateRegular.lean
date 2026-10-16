/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Algebra.Category.Ring.Basic

/-! # Regularity of four bivariate polynomial equations over any commutative ring -/
@[expose] public section
universe u
namespace AlgebraicGeometry.Scheme.ProjectiveLine
open scoped nonZeroDivisors
/-- The first diagonal equation is regular over every base ring. -/
theorem diagonalPolynomial_plus_plus_regular (R : CommRingCat.{u}) :
    (Polynomial.C Polynomial.X - Polynomial.X : Polynomial (Polynomial R)) ∈
      (Polynomial (Polynomial R))⁰ := by
  apply Polynomial.mem_nonzeroDivisors_of_coeff_mem 1
  simp [mem_nonZeroDivisors_iff]
/-- The first mixed diagonal equation has a unit constant coefficient. -/
theorem diagonalPolynomial_plus_minus_regular (R : CommRingCat.{u}) :
    (Polynomial.C Polynomial.X * Polynomial.X - 1 : Polynomial (Polynomial R)) ∈
      (Polynomial (Polynomial R))⁰ := by
  apply Polynomial.mem_nonzeroDivisors_of_coeff_mem 0
  simp [mem_nonZeroDivisors_iff]
/-- The second mixed diagonal equation has a unit constant coefficient. -/
theorem diagonalPolynomial_minus_plus_regular (R : CommRingCat.{u}) :
    (1 - Polynomial.C Polynomial.X * Polynomial.X : Polynomial (Polynomial R)) ∈
      (Polynomial (Polynomial R))⁰ := by
  apply Polynomial.mem_nonzeroDivisors_of_coeff_mem 0
  simp
/-- The second diagonal equation is monic in the second variable. -/
theorem diagonalPolynomial_minus_minus_regular (R : CommRingCat.{u}) :
    (Polynomial.X - Polynomial.C Polynomial.X : Polynomial (Polynomial R)) ∈
      (Polynomial (Polynomial R))⁰ := by
  apply Polynomial.mem_nonzeroDivisors_of_coeff_mem 1
  simp
end AlgebraicGeometry.Scheme.ProjectiveLine
