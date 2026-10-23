/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/

module

public import Aglib.Algebra.Homology.ModuleCat.LaurentProjectorCech
public import Mathlib.Data.ZMod.Basic

/-! # Consumers of actual projector-image Laurent Cech models

The tests retain the literal image inclusions, chart retractions, signed cutoff and shifted
original differential. Constant coefficient idempotents include the nonzero proper idempotent
three over ZMod six, so the result is not restricted to identity projectors.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Polynomial LaurentPolynomial
open scoped LaurentPolynomial Matrix
universe u
namespace QuillenTest.LaurentProjectorModel

open LaurentPolynomial.Projector ModuleCat
variable {R : Type u} [CommRing R]

/-- The original constant rank-one polynomial projector. -/
def polynomialProjector (e : R) : Matrix (Fin 1) (Fin 1) R[X] := fun _ _ => Polynomial.C e

/-- The original constant Laurent transition on the projector image. -/
def laurentProjector (e : R) : Matrix (Fin 1) (Fin 1) R[T;T⁻¹] := fun _ _ => LaurentPolynomial.C e

/-- The actual coefficient idempotent gives a polynomial matrix idempotent. -/
theorem polynomialProjector_idempotent (e : R) (he : e * e = e) :
    polynomialProjector e * polynomialProjector e = polynomialProjector e := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.mul_apply, Fin.sum_univ_one, polynomialProjector]
  rw [← Polynomial.C_mul, he]

/-- The actual coefficient idempotent gives a Laurent matrix idempotent. -/
theorem laurentProjector_idempotent (e : R) (he : e * e = e) :
    laurentProjector e * laurentProjector e = laurentProjector e := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.mul_apply, Fin.sum_univ_one, laurentProjector]
  rw [← map_mul, he]

/-- Positive restriction retains the literal constant transition matrix. -/
theorem plusMatrix_projector (e : R) :
    plusMatrix (polynomialProjector e) = laurentProjector e := by
  ext i j
  simp [plusMatrix, polynomialProjector, laurentProjector]

/-- Negative restriction retains the same literal constant transition matrix. -/
theorem minusMatrix_projector (e : R) :
    minusMatrix (polynomialProjector e) = laurentProjector e := by
  ext i j
  simp [minusMatrix, polynomialProjector, laurentProjector]

/-- Every specified coefficient idempotent has a genuine image-module Cech model. -/
theorem idempotent_cech_model (e : R) (he : e * e = e) :
    ∃ (hp : polynomialProjector e * polynomialProjector e = polynomialProjector e)
      (hpg : plusMatrix (polynomialProjector e) * laurentProjector e = laurentProjector e),
    ∃ P : CochainComplex (ModuleCat.{u} R) ℤ,
      (∀ n, n ≠ 0 → n ≠ 1 → IsZero (P.X n)) ∧
      (∀ n, Module.Finite R (P.X n) ∧ Module.Projective R (P.X n)) ∧
      Nonempty (HomotopyEquiv (linearMapCechComplex
        (rangeDifference (polynomialProjector e) (polynomialProjector e)
          (laurentProjector e) hp hpg)) P) := by
  have hp := polynomialProjector_idempotent e he
  have hpg : plusMatrix (polynomialProjector e) * laurentProjector e = laurentProjector e := by
    rw [plusMatrix_projector, laurentProjector_idempotent e he]
  refine ⟨hp, hpg, ?_⟩
  apply exists_projector_cech_model _ _ _ (laurentProjector e) hp hp hpg
  · rw [laurentProjector_idempotent e he, plusMatrix_projector]
  · rw [laurentProjector_idempotent e he, minusMatrix_projector]
  · rw [minusMatrix_projector, laurentProjector_idempotent e he]

/-- The nonzero proper idempotent three in ZMod six has an actual Cech model. -/
theorem nontrivial_idempotent_model :
    ∃ (hp : polynomialProjector (3 : ZMod 6) * polynomialProjector 3 = polynomialProjector 3)
      (hpg : plusMatrix (polynomialProjector (3 : ZMod 6)) * laurentProjector 3 =
        laurentProjector 3),
    ∃ P : CochainComplex (ModuleCat (ZMod 6)) ℤ,
      (∀ n, n ≠ 0 → n ≠ 1 → IsZero (P.X n)) ∧
      (∀ n, Module.Finite (ZMod 6) (P.X n) ∧ Module.Projective (ZMod 6) (P.X n)) ∧
      Nonempty (HomotopyEquiv (linearMapCechComplex
        (rangeDifference (polynomialProjector 3) (polynomialProjector 3)
          (laurentProjector 3) hp hpg)) P) :=
  idempotent_cech_model 3 (by decide)

variable {ι κ : Type u} [Fintype ι] [Fintype κ]

/-- Forgetting the actual image inclusions recovers the literal signed chart differential. -/
theorem original_range_difference (p : Matrix ι ι R[X]) (q : Matrix κ κ R[X])
    (g : Matrix ι κ R[T;T⁻¹]) (hp : p * p = p) (hpg : plusMatrix p * g = g)
    (x : LinearMap.range (polynomialAction p) × LinearMap.range (polynomialAction q)) :
    (rangeDifference p q g hp hpg x).val =
      LaurentPolynomial.Cutoff.plusEmbedding x.1.val -
        action g (LaurentPolynomial.Cutoff.minusEmbedding x.2.val) := rfl

/-- The original polynomial inclusion and projector give the actual chart-module retraction. -/
theorem original_chart_retraction (p : Matrix ι ι R[X]) (hp : p * p = p) :
    (polynomialAction p).rangeRestrict.comp (LinearMap.range (polynomialAction p)).subtype =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact polynomialRange_fixed p hp x

/-- The projected negative coordinate keeps the original minus sign and inverse transition. -/
theorem original_parametrix_negative (p : Matrix ι ι R[X]) (q : Matrix κ κ R[X])
    (h : Matrix κ ι R[T;T⁻¹]) (x : LinearMap.range (action (plusMatrix p))) :
    (rangeParametrix p q h x).2.val = -polynomialAction q
      (LaurentPolynomial.Cutoff.minusCutoff
        (action h (LaurentPolynomial.Cutoff.negativeRemainder x.val))) := rfl

/-- The shifted source and target isomorphisms retain the original restricted differential. -/
theorem original_shifted_difference (p : Matrix ι ι R[X]) (q : Matrix κ κ R[X])
    (g : Matrix ι κ R[T;T⁻¹]) (hp : p * p = p) (hpg : plusMatrix p * g = g) :
    (linearMapCechSourceIso (rangeDifference p q g hp hpg)).hom ≫
        (linearMapCechComplex (rangeDifference p q g hp hpg)).d 0 1 =
      ModuleCat.ofHom (rangeDifference p q g hp hpg) ≫
        (linearMapCechTargetIso (rangeDifference p q g hp hpg)).hom :=
  linearMapCechSource_d _

end QuillenTest.LaurentProjectorModel
