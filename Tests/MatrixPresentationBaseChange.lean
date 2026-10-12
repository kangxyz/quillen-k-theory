/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Algebra.Module.MatrixBaseChange
public import Quillen.Algebra.Polynomial.LaurentMatrixProjector

/-! # Original matrix presentations and the two Laurent scalar maps

These consumers retain the original retract and overlap maps. The positive and negative
polynomial algebra structures on Laurent polynomials are installed separately and explicitly.
Their pure-tensor variable formulas are respectively T and its inverse, and their projector
matrices are exactly the previously defined positive and negative chart matrices.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Polynomial LaurentPolynomial Module.Projective
open scoped TensorProduct LaurentPolynomial Matrix
universe u v
namespace Quillen.Tests.MatrixPresentationBaseChange
variable {R : Type u} [CommRing R]

/-- The actual image equivalence retains the specified inclusion and retraction on both sides. -/
theorem original_image_maps {M : Type v} [AddCommGroup M] [Module R M] {n : ℕ}
    (i : M →ₗ[R] Fin n → R) (r : (Fin n → R) →ₗ[R] M)
    (h : r.comp i = LinearMap.id) (x : M)
    (y : LinearMap.range (retractMatrix i r).mulVecLin) :
    (retractMatrixImageIso i r h x).val = i x ∧
      (retractMatrixImageIso i r h).symm y = r y.val := ⟨rfl, rfl⟩

/-- The original overlap equivalence is retained when acting on the actual chart inclusion. -/
theorem original_transition {M N : Type v} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {m n : ℕ}
    (i : M →ₗ[R] Fin m → R) (j : N →ₗ[R] Fin n → R)
    (s : (Fin n → R) →ₗ[R] N) (hs : s.comp j = LinearMap.id)
    (e : N ≃ₗ[R] M) (x : N) :
    transitionMatrix i s e *ᵥ j x = i (e x) :=
  transitionMatrix_inclusion i j s e hs x

section Positive
/-- The actual positive polynomial-to-Laurent scalar map. -/
local instance positivePolynomialAlgebra : Algebra R[X] R[T;T⁻¹] :=
  (Polynomial.toLaurent : R[X] →+* R[T;T⁻¹]).toAlgebra

/-- Positive scalar extension uses the original noninverted polynomial restriction. -/
theorem positive_pureTensor {n : ℕ} (a : R[T;T⁻¹]) (x : Fin n → R[X]) (j : Fin n) :
    TensorProduct.piScalarRight R[X] R[T;T⁻¹] R[T;T⁻¹] (Fin n) (a ⊗ₜ[R[X]] x) j =
      toLaurent (x j) * a := by
  rw [TensorProduct.piScalarRight_tmul_apply]
  rfl

/-- The positive polynomial variable is sent to the original Laurent variable. -/
theorem positive_variable :
    TensorProduct.piScalarRight R[X] R[T;T⁻¹] R[T;T⁻¹] (Fin 1)
      ((1 : R[T;T⁻¹]) ⊗ₜ[R[X]] (fun _ => (X : R[X]))) 0 = T 1 := by
  rw [positive_pureTensor]
  simp

/-- Positive scalar extension yields the literal positive chart projector matrix. -/
theorem positive_projector_matrix {M : Type v} [AddCommGroup M] [Module R[X] M] {n : ℕ}
    (i : M →ₗ[R[X]] Fin n → R[X]) (r : (Fin n → R[X]) →ₗ[R[X]] M) :
    retractMatrix (baseChangeInclusion R[T;T⁻¹] i) (baseChangeRetraction R[T;T⁻¹] r) =
      Quillen.LaurentProjector.plusMatrix (retractMatrix i r) :=
  baseChange_retractMatrix R[T;T⁻¹] i r
end Positive

section Negative
/-- The actual negative polynomial-to-Laurent scalar map includes variable inversion. -/
local instance negativePolynomialAlgebra : Algebra R[X] R[T;T⁻¹] :=
  ((LaurentPolynomial.invert : R[T;T⁻¹] ≃ₐ[R] R[T;T⁻¹]).toAlgHom.toRingHom.comp
    (Polynomial.toLaurent : R[X] →+* R[T;T⁻¹])).toAlgebra

/-- Scalar multiplication on the negative Laurent chart uses the same explicit inverse map. -/
local instance negativePolynomialSMul : SMul R[X] R[T;T⁻¹] :=
  (negativePolynomialAlgebra (R := R)).toSMul

/-- The negative-chart module structure is induced by that exact algebra structure. -/
local instance negativePolynomialModule : Module R[X] R[T;T⁻¹] :=
  @Algebra.toModule R[X] R[T;T⁻¹] _ _ (negativePolynomialAlgebra (R := R))

/-- Negative scalar extension retains the original inversion on every pure tensor. -/
theorem negative_pureTensor {n : ℕ} (a : R[T;T⁻¹]) (x : Fin n → R[X]) (j : Fin n) :
    TensorProduct.piScalarRight R[X] R[T;T⁻¹] R[T;T⁻¹] (Fin n) (a ⊗ₜ[R[X]] x) j =
      invert (toLaurent (x j)) * a := by
  rw [TensorProduct.piScalarRight_tmul_apply]
  rfl

/-- The negative polynomial variable is sent to the inverse original Laurent variable. -/
theorem negative_variable :
    TensorProduct.piScalarRight R[X] R[T;T⁻¹] R[T;T⁻¹] (Fin 1)
      ((1 : R[T;T⁻¹]) ⊗ₜ[R[X]] (fun _ => (X : R[X]))) 0 = T (-1) := by
  rw [negative_pureTensor]
  simp

/-- Negative scalar extension yields the literal inverse-coordinate chart projector matrix. -/
theorem negative_projector_matrix {M : Type v} [AddCommGroup M] [Module R[X] M] {n : ℕ}
    (i : M →ₗ[R[X]] Fin n → R[X]) (r : (Fin n → R[X]) →ₗ[R[X]] M) :
    retractMatrix (baseChangeInclusion R[T;T⁻¹] i) (baseChangeRetraction R[T;T⁻¹] r) =
      Quillen.LaurentProjector.minusMatrix (retractMatrix i r) :=
  baseChange_retractMatrix R[T;T⁻¹] i r
end Negative

end Quillen.Tests.MatrixPresentationBaseChange
