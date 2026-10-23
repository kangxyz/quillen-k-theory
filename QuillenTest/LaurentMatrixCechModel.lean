/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/

module

public import Quillen.Aglib.Algebra.Homology.ModuleCat.LaurentCech
public import Quillen.Aglib.Algebra.Polynomial.Laurent.Cech
public import Mathlib.Data.ZMod.Basic

/-! # Consumers of finite Laurent-matrix Cech models

These tests retain the original restriction order, actual coefficient inclusions, both
finite defects, and the explicit shifted coordinate square. Rank-one twisting recovers the
existing scalar differential. Nonreduced and zero rings, including empty rank, are covered.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Polynomial LaurentPolynomial LaurentPolynomial.Cutoff ModuleCat
open scoped LaurentPolynomial Matrix
universe u v
namespace QuillenTest.LaurentMatrixCechModel

open Quillen
variable {R : Type u} [CommRing R]

/-- Each coordinate retains the literal positive-minus-transition-times-negative map. -/
theorem original_difference_coordinate {ι : Type v} [Fintype ι]
    (g : Matrix ι ι R[T;T⁻¹]) (a b : ι → R[X]) (i : ι) :
    matrixDifference g (a,b) i = toLaurent (a i) -
      ∑ j, g i j * invert (toLaurent (b j)) := rfl

/-- The actual rank-one twisting matrix in the specified chart bases. -/
def transition (d : ℤ) : Matrix (Fin 1) (Fin 1) R[T;T⁻¹] := fun _ _ => T d

/-- The original rank-one transition has the actual opposite-power inverse. -/
theorem transition_inverse (d : ℤ) : transition (R := R) d * transition (-d) = 1 := by
  apply Matrix.ext
  intro i j
  have hij : i = j := Subsingleton.elim _ _
  subst j
  simp only [Matrix.mul_apply, Fin.sum_univ_one, transition, Matrix.one_apply]
  rw [← T_add, add_neg_cancel, T_zero]
  simp

/-- Rank one recovers the existing original scalar Cech restriction difference. -/
theorem original_scalar_difference (d : ℤ) (a b : R[X]) :
    matrixDifference (transition (R := R) d) ((fun _ => a), (fun _ => b)) 0 =
      Quillen.PolynomialLaurentCech.difference R d (a,b) := by
  simp [original_difference_coordinate, transition,
    Quillen.PolynomialLaurentCech.difference_apply]

/-- The actual right defect has a finite coefficient factor without an assumed finite-band bound. -/
theorem original_finite_right_defect {ι : Type v} [Fintype ι]
    (g h : Matrix ι ι R[T;T⁻¹]) :
    ∃ N : ℕ, ∃ r : (ι → R[T;T⁻¹]) →ₗ[R] (ι → Fin N → R),
      (rightWindowInclusion g N).comp r = matrixRightDefect g h := by
  obtain ⟨N, hN⟩ := exists_matrix_negative_bound h
  exact ⟨N, rightWindowCoefficients h N hN, right_window_defect_factorization g h N hN⟩

/-- The literal left chart factors satisfy the original defect identity. -/
theorem original_left_defect {ι : Type v} [Fintype ι] [DecidableEq ι]
    (g h : Matrix ι ι R[T;T⁻¹]) (hhg : h * g = 1) (a b : ι → R[X]) :
    matrixParametrix h (matrixDifference g (a,b)) +
      matrixLeftColumns h (matrixNegativeTrunc g b) = (a,b) :=
  LinearMap.congr_fun (matrix_left_defect g h hhg) (a,b)

/-- The explicit source and target coordinate isomorphisms keep the original degree-zero map. -/
theorem original_shifted_differential {ι : Type v} [Fintype ι]
    (g : Matrix ι ι R[T;T⁻¹]) :
    (linearMapCechSourceIso (matrixDifference g)).hom ≫
        (linearMapCechComplex (matrixDifference g)).d 0 1 =
      ModuleCat.ofHom (matrixDifference g) ≫ (linearMapCechTargetIso (matrixDifference g)).hom :=
  linearMapCechSource_d _

/-- Every actual scalar twisting transition has a genuine finite-projective Cech model. -/
theorem twisting_model (d : ℤ) :
    ∃ P : CochainComplex (ModuleCat.{u} R) ℤ,
      (∀ n, n ≠ 0 → n ≠ 1 → IsZero (P.X n)) ∧
      (∀ n, Module.Finite R (P.X n) ∧ Module.Projective R (P.X n)) ∧
      Nonempty (HomotopyEquiv (linearMapCechComplex (matrixDifference (transition d))) P) := by
  apply exists_matrix_cech_finite_projective_model (transition d) (transition (-d))
    (transition_inverse d)
  simpa using transition_inverse (R := R) (-d)

/-- Nilpotent coefficients cause no field or domain restriction on the actual model. -/
theorem nonreduced_model :
    ∃ P : CochainComplex (ModuleCat (ZMod 4)) ℤ,
      (∀ n, n ≠ 0 → n ≠ 1 → IsZero (P.X n)) ∧
      (∀ n, Module.Finite (ZMod 4) (P.X n) ∧ Module.Projective (ZMod 4) (P.X n)) ∧
      Nonempty (HomotopyEquiv
        (linearMapCechComplex (matrixDifference (transition (R := ZMod 4) 2))) P) :=
  twisting_model 2

/-- Empty rank over the zero ring retains the original identity transition and actual model. -/
theorem zero_ring_empty_rank_model :
    ∃ P : CochainComplex (ModuleCat (ZMod 1)) ℤ,
      (∀ n, n ≠ 0 → n ≠ 1 → IsZero (P.X n)) ∧
      (∀ n, Module.Finite (ZMod 1) (P.X n) ∧ Module.Projective (ZMod 1) (P.X n)) ∧
      Nonempty (HomotopyEquiv (linearMapCechComplex
        (matrixDifference (1 : Matrix (Fin 0) (Fin 0) (ZMod 1)[T;T⁻¹]))) P) :=
  exists_matrix_cech_finite_projective_model 1 1 (by simp) (by simp)

end QuillenTest.LaurentMatrixCechModel
