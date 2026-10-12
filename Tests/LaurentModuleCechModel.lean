/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Algebra.ModuleComplex.LaurentModuleCech
public import Mathlib.Data.ZMod.Basic

/-! # Original finite-projective Laurent chart complexes

Consumers retain both distinct scalar maps, the original overlap arrow and signed differential,
and actual chain maps and homotopies in degrees zero and one.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex ModuleCat
open Polynomial LaurentPolynomial Quillen.LaurentProjector Quillen.ModuleComplex
open scoped ChangeOfRings LaurentPolynomial
universe u
namespace Quillen.Tests.LaurentModuleCechModel
variable {R : Type u} [CommRing R]

/-- The free chart fixture uses the actual polynomial module. -/
abbrev freeChart (R : Type u) [CommRing R] (n : ℕ) : ModuleCat.{u} R[X] :=
  ModuleCat.of R[X] (Fin n → R[X])

/-- The overlap compares two distinct actual scalar extensions through their original bases. -/
def standardOverlap (R : Type u) [CommRing R] (n : ℕ) :
    (extendScalars (negativeScalarMap R)).obj (freeChart R n) ≅
      (extendScalars (Polynomial.toLaurent (R := R))).obj (freeChart R n) :=
  extendScalarsPiIso (negativeScalarMap R) n ≪≫
    (extendScalarsPiIso (Polynomial.toLaurent (R := R)) n).symm

/-- The negative variable remains inverted after transport into the positive overlap module. -/
theorem original_negative_variable :
    (extendScalarsPiIso (Polynomial.toLaurent (R := R)) 1).hom
      ((standardOverlap R 1).hom
        ((1 : R[T;T⁻¹]) ⊗ₜ[R[X],negativeScalarMap R] (fun _ : Fin 1 => (X : R[X])))) 0 =
      T (-1) := by
  change (extendScalarsPiIso (Polynomial.toLaurent (R := R)) 1).hom
    ((extendScalarsPiIso (Polynomial.toLaurent (R := R)) 1).inv
      ((extendScalarsPiIso (negativeScalarMap R) 1).hom _)) 0 = _
  erw [Iso.inv_hom_id_apply]
  rw [extendScalarsPiIso_tmul]
  simp [negativeScalarMap]

/-- The positive variable uses the noninverted scalar map in the same environment. -/
theorem original_positive_variable :
    (extendScalarsPiIso (Polynomial.toLaurent (R := R)) 1).hom
      ((1 : R[T;T⁻¹]) ⊗ₜ[R[X],Polynomial.toLaurent] (fun _ : Fin 1 => (X : R[X]))) 0 =
      T 1 := by
  rw [extendScalarsPiIso_tmul]
  simp

/-- The original differential subtracts the transported negative unit from the positive unit. -/
theorem original_signed_units (M N : ModuleCat.{u} R[X])
    (e : (extendScalars (negativeScalarMap R)).obj N ≅
      (extendScalars (Polynomial.toLaurent (R := R))).obj M)
    (a : (restrictScalars (Polynomial.C : R →+* R[X])).obj M)
    (b : (restrictScalars (Polynomial.C : R →+* R[X])).obj N) :
    moduleDifference (R := R) M N e (a,b) =
      @Sub.sub ((extendScalars (Polynomial.toLaurent (R := R))).obj M) inferInstance
        ((1 : R[T;T⁻¹]) ⊗ₜ[R[X],Polynomial.toLaurent] (a : M))
        (e.hom ((1 : R[T;T⁻¹]) ⊗ₜ[R[X],negativeScalarMap R] (b : N))) :=
  moduleDifference_apply M N e a b

/-- The shifted-cone coordinates retain the original differential in degrees zero and one. -/
theorem original_cochain_differential (M N : ModuleCat.{u} R[X])
    (e : (extendScalars (negativeScalarMap R)).obj N ≅
      (extendScalars (Polynomial.toLaurent (R := R))).obj M) :
    (linearMapCechSourceIso (moduleDifference (R := R) M N e)).hom ≫
        (linearMapCechComplex (moduleDifference (R := R) M N e)).d 0 1 =
      ModuleCat.ofHom (moduleDifference (R := R) M N e) ≫
        (linearMapCechTargetIso (moduleDifference (R := R) M N e)).hom :=
  linearMapCechSource_d _

/-- Original chart inclusions transport the exact signed differential to its rectangular matrix. -/
theorem original_coordinate_square (M N : ModuleCat.{u} R[X]) {m n : ℕ}
    (i : M →ₗ[R[X]] Fin m → R[X]) (j : N →ₗ[R[X]] Fin n → R[X])
    (s : (Fin n → R[X]) →ₗ[R[X]] N) (hs : s.comp j = LinearMap.id)
    (e : (extendScalars (negativeScalarMap R)).obj N ≅
      (extendScalars (Polynomial.toLaurent (R := R))).obj M)
    (a : (restrictScalars (Polynomial.C : R →+* R[X])).obj M)
    (b : (restrictScalars (Polynomial.C : R →+* R[X])).obj N) :
    extendScalarsInclusion (Polynomial.toLaurent (R := R)) i
        (moduleDifference (R := R) M N e (a,b)) =
      Quillen.LaurentCutoff.plusEmbedding (i a) - action
        (extensionTransitionMatrix (Polynomial.toLaurent (R := R)) (negativeScalarMap R) i s e)
        (Quillen.LaurentCutoff.minusEmbedding (j b)) :=
  moduleDifference_coordinates M N i j s hs e a b

/-- Actual forward and reverse chain maps have both homotopies, with no chart-freeness premise. -/
theorem original_chain_maps (M N : ModuleCat.{u} R[X])
    [Module.Finite R[X] M] [Module.Projective R[X] M]
    [Module.Finite R[X] N] [Module.Projective R[X] N]
    (e : (extendScalars (negativeScalarMap R)).obj N ≅
      (extendScalars (Polynomial.toLaurent (R := R))).obj M) :
    ∃ P : CochainComplex (ModuleCat.{u} R) ℤ,
      (∀ k, k ≠ 0 → k ≠ 1 → IsZero (P.X k)) ∧
      (∀ k, Module.Finite R (P.X k) ∧ Module.Projective R (P.X k)) ∧
      ∃ f : linearMapCechComplex (moduleDifference (R := R) M N e) ⟶ P,
      ∃ g : P ⟶ linearMapCechComplex (moduleDifference (R := R) M N e),
      Nonempty (Homotopy (f ≫ g) (𝟙 _)) ∧ Nonempty (Homotopy (g ≫ f) (𝟙 _)) := by
  obtain ⟨P, hP, hfin, ⟨h⟩⟩ := exists_moduleDifference_model_of_finite_projective M N e
  exact ⟨P, hP, hfin, h.hom, h.inv, ⟨h.homotopyHomInvId⟩, ⟨h.homotopyInvHomId⟩⟩

/-- Nonreduced coefficients retain the actual original overlap isomorphism and model. -/
theorem nonreduced_model :
    ∃ P : CochainComplex (ModuleCat (ZMod 4)) ℤ,
      (∀ k, k ≠ 0 → k ≠ 1 → IsZero (P.X k)) ∧
      (∀ k, Module.Finite (ZMod 4) (P.X k) ∧ Module.Projective (ZMod 4) (P.X k)) ∧
      Nonempty (HomotopyEquiv (linearMapCechComplex
        (moduleDifference (freeChart (ZMod 4) 1) (freeChart (ZMod 4) 1)
          (standardOverlap (ZMod 4) 1))) P) :=
  exists_moduleDifference_model_of_finite_projective _ _ _

/-- The empty polynomial module over the zero ring has the same actual two-term comparison. -/
theorem zero_ring_empty_model :
    ∃ P : CochainComplex (ModuleCat (ZMod 1)) ℤ,
      (∀ k, k ≠ 0 → k ≠ 1 → IsZero (P.X k)) ∧
      (∀ k, Module.Finite (ZMod 1) (P.X k) ∧ Module.Projective (ZMod 1) (P.X k)) ∧
      Nonempty (HomotopyEquiv (linearMapCechComplex
        (moduleDifference (freeChart (ZMod 1) 0) (freeChart (ZMod 1) 0)
          (standardOverlap (ZMod 1) 0))) P) :=
  exists_moduleDifference_model_of_finite_projective _ _ _

end Quillen.Tests.LaurentModuleCechModel
