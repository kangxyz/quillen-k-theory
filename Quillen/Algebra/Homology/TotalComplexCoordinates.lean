/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # Finite coordinates in the actual first-quadrant total complex -/
@[expose] public section
noncomputable section
open CategoryTheory Limits
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.HomologicalAlgebra

/-- The actual finite antidiagonal indexing a total degree. -/
abbrev TotalDegree (n : ℕ) :=
  ((ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) ⁻¹' ({n} : Set ℕ))

/-- Enumerate a first-quadrant antidiagonal without changing its original indices. -/
def totalDegreeEquiv (n : ℕ) : Fin (n + 1) ≃ TotalDegree n where
  toFun i := ⟨(i.val, n - i.val), by change i.val + (n - i.val) = n; have := i.isLt; omega⟩
  invFun p := ⟨p.val.1, by have hp : p.val.1 + p.val.2 = n := p.property; omega⟩
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · dsimp
      have hp : p.val.1 + p.val.2 = n := p.property
      omega

/-- Each total degree has finitely many first-quadrant summands. -/
instance (n : ℕ) : Fintype (TotalDegree n) := Fintype.ofEquiv _ (totalDegreeEquiv n)

variable (K : HomologicalComplex₂ (ModuleCat.{u} ℤ)
  (ComplexShape.down ℕ) (ComplexShape.down ℕ))

/-- Projection onto an original summand of the actual total complex. -/
def totalCoordinate (n : ℕ) (p : TotalDegree n) :
    (K.total (ComplexShape.down ℕ)).X n ⟶ (K.X p.val.1).X p.val.2 :=
  Sigma.π (K.toGradedObject.mapObjFun
    (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)) n) p

/-- Inclusion of the original antidiagonal summand. -/
def totalSummand (n : ℕ) (p : TotalDegree n) :
    (K.X p.val.1).X p.val.2 ⟶ (K.total (ComplexShape.down ℕ)).X n :=
  K.ιTotal (ComplexShape.down ℕ) p.val.1 p.val.2 n p.property

/-- The actual summand projection is a retraction of its original inclusion. -/
@[reassoc (attr := simp)]
theorem totalSummand_coordinate_self (n : ℕ) (p : TotalDegree n) :
    totalSummand K n p ≫ totalCoordinate K n p = 𝟙 _ := by
  change Sigma.ι _ p ≫ Sigma.π _ p = _
  rw [Sigma.ι_π]
  simp only [dite_true, eqToHom_refl]
  rfl

/-- Distinct total summands have zero cross-coordinate maps. -/
@[reassoc (attr := simp)]
theorem totalSummand_coordinate_ne (n : ℕ) (p q : TotalDegree n) (h : p ≠ q) :
    totalSummand K n p ≫ totalCoordinate K n q = 0 := by
  change Sigma.ι _ p ≫ Sigma.π _ q = _
  rw [Sigma.ι_π]
  simp [h]

/-- Finite antidiagonal coordinates reconstruct the actual total module. -/
theorem totalCoordinate_sum (n : ℕ) :
    ∑ p : TotalDegree n, totalCoordinate K n p ≫ totalSummand K n p = 𝟙 _ := by
  classical
  apply Sigma.hom_ext
  intro p
  change totalSummand K n p ≫ _ = totalSummand K n p ≫ _
  rw [Preadditive.comp_sum]
  simp only [Category.comp_id, ← Category.assoc]
  rw [Finset.sum_eq_single p]
  · rw [totalSummand_coordinate_self, Category.id_comp]
  · intro q _ hq
    rw [totalSummand_coordinate_ne K n p q hq.symm, zero_comp]
  · simp

/-- The actual total differential has its two signed summand components. -/
theorem totalSummand_d (n m : ℕ) (p : TotalDegree n) :
    totalSummand K n p ≫ (K.total (ComplexShape.down ℕ)).d n m =
      K.d₁ (ComplexShape.down ℕ) p.val.1 p.val.2 m +
        K.d₂ (ComplexShape.down ℕ) p.val.1 p.val.2 m := by
  rw [HomologicalComplex₂.total_d, Preadditive.comp_add]
  exact congrArg₂ (· + ·) (K.ι_D₁ _ _ _ _ _ _) (K.ι_D₂ _ _ _ _ _ _)

/-- Actual coordinates separate elements of every total module. -/
theorem totalCoordinate_ext (n : ℕ) (x y : (K.total (ComplexShape.down ℕ)).X n)
    (h : ∀ p : TotalDegree n, totalCoordinate K n p x = totalCoordinate K n p y) : x = y := by
  have hx := congrArg (fun f => f x) (totalCoordinate_sum K n)
  have hy := congrArg (fun f => f y) (totalCoordinate_sum K n)
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.comp_apply,
    ModuleCat.id_apply] at hx hy
  rw [← hx, ← hy]
  exact Finset.sum_congr rfl (fun p _ => congrArg (totalSummand K n p) (h p))

end Quillen.HomologicalAlgebra
