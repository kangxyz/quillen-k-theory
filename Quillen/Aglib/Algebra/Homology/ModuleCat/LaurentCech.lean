/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.Algebra.Polynomial.Laurent.MatrixCech
public import Quillen.Aglib.Algebra.Homology.ModuleCat.LinearMapConeShift
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-! # Finite-projective models of actual finite Laurent-matrix Cech complexes

Both finite-window factorizations are discharged for specified inverse Laurent matrices.
The actual parametrix kernel gives a bounded finite-projective model and an explicit
cochain homotopy equivalence. The degree-zero/one version retains the original shift,
source sign and differential. Rings may be nonreduced or zero. A comparison with a
geometric sheaf's chosen chart trivializations is a separate obligation.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Polynomial LaurentPolynomial
open scoped LaurentPolynomial Matrix
universe u v
namespace Quillen.LaurentCutoff
open Quillen.ModuleComplex
variable {R : Type u} [CommRing R] {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- An actual invertible finite Laurent matrix gives a finite-projective model
of its literal signed two-chart differential cone. -/
theorem exists_matrix_finite_projective_model
    (g h : Matrix ι ι R[T;T⁻¹]) (hgh : g * h = 1) (hhg : h * g = 1) :
    ∃ P : CochainComplex (ModuleCat.{max u v} R) ℤ,
      (∀ n, n ≠ -1 → n ≠ 0 → IsZero (P.X n)) ∧
      (∀ n, Module.Finite R (P.X n) ∧ Module.Projective R (P.X n)) ∧
      Nonempty (HomotopyEquiv (linearMapCone (matrixDifference g)) P) := by
  obtain ⟨N, hN⟩ := exists_matrix_negative_bound g
  obtain ⟨M, hM⟩ := exists_matrix_negative_bound h
  apply exists_finite_projective_parametrix_model (matrixDifference g) (matrixParametrix h)
    (rightWindowInclusion g M) (rightWindowCoefficients h M hM) ?_
    ((matrixLeftColumns h).comp (windowEmbedding N))
    ((matrixWindowCoefficients g N hN).comp (LinearMap.snd R (ι → R[X]) (ι → R[X]))) ?_
  · rw [right_window_defect_factorization]
    exact matrix_right_defect g h hgh
  · rw [left_window_defect_factorization]
    exact matrix_left_defect g h hhg

end Quillen.LaurentCutoff

namespace Quillen.LaurentCutoff
open Quillen.ModuleComplex
variable {R : Type u} [CommRing R] {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- The genuine signed matrix Cech differential has a finite-projective model
in degrees zero and one. -/
theorem exists_matrix_cech_finite_projective_model
    (g h : Matrix ι ι R[T;T⁻¹]) (hgh : g * h = 1) (hhg : h * g = 1) :
    ∃ P : CochainComplex (ModuleCat.{max u v} R) ℤ,
      (∀ n, n ≠ 0 → n ≠ 1 → IsZero (P.X n)) ∧
      (∀ n, Module.Finite R (P.X n) ∧ Module.Projective R (P.X n)) ∧
      Nonempty (HomotopyEquiv (linearMapCechComplex (matrixDifference g)) P) := by
  obtain ⟨P, hP, hf, ⟨e⟩⟩ := exists_matrix_finite_projective_model g h hgh hhg
  refine ⟨P⟦(-1 : ℤ)⟧, ?_, ?_, ?_⟩
  · intro n h0 h1
    exact hP (n + -1) (by omega) (by omega)
  · intro n
    exact hf (n + -1)
  · refine ⟨{
      hom := e.hom⟦(-1 : ℤ)⟧'
      inv := e.inv⟦(-1 : ℤ)⟧'
      homotopyHomInvId := ?_
      homotopyInvHomId := ?_ }⟩
    · simpa only [linearMapCechComplex, CategoryTheory.Functor.map_comp,
        CategoryTheory.Functor.map_id]
        using e.homotopyHomInvId.shift (-1)
    · simpa only [linearMapCechComplex, CategoryTheory.Functor.map_comp,
        CategoryTheory.Functor.map_id]
        using e.homotopyInvHomId.shift (-1)

end Quillen.LaurentCutoff
