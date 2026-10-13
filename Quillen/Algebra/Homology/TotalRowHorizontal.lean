/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Algebra.Homology.TotalRowHomotopy

/-! # The strictly lower triangular horizontal correction of a total row homotopy -/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Quillen.HomologicalAlgebra

variable (K : HomologicalComplex₂ (ModuleCat.{u} ℤ)
  (ComplexShape.down ℕ) (ComplexShape.down ℕ))

/-- The contribution of the outer differential to a total row homotopy. -/
def totalRowHorizontal (h : RowHomotopyData K) (n : ℕ) :
    (K.total (ComplexShape.down ℕ)).X n ⟶ (K.total (ComplexShape.down ℕ)).X n :=
  (show (K.total (ComplexShape.down ℕ)).X n ⟶
      (K.total (ComplexShape.down ℕ)).X n from
    K.D₁ (ComplexShape.down ℕ) n ((ComplexShape.down ℕ).next n) ≫
      totalRowHomotopy K h ((ComplexShape.down ℕ).next n) n) +
    (show (K.total (ComplexShape.down ℕ)).X n ⟶
        (K.total (ComplexShape.down ℕ)).X n from
      totalRowHomotopy K h n ((ComplexShape.down ℕ).prev n) ≫
        K.D₁ (ComplexShape.down ℕ) ((ComplexShape.down ℕ).prev n) n)

/-- Original summands with different outer degrees have zero cross-coordinate maps. -/
@[reassoc]
theorem ιTotal_coordinate_ne_outer (n i p : ℕ) (hip : i + p = n)
    (q : TotalDegree n) (hiq : i ≠ q.val.1) :
    K.ιTotal (ComplexShape.down ℕ) i p n hip ≫ totalCoordinate K n q = 0 := by
  apply totalSummand_coordinate_ne K n ⟨(i, p), hip⟩ q
  intro heq
  exact hiq (congrArg (fun a : TotalDegree n ↦ a.val.1) heq)

/-- A row homotopy never changes the outer degree. -/
@[reassoc]
theorem ιTotal_totalRowHomotopy_coordinate (h : RowHomotopyData K)
    (n m i p : ℕ) (hip : i + p = n) (q : TotalDegree m) (hiq : i ≠ q.val.1) :
    K.ιTotal (ComplexShape.down ℕ) i p n hip ≫
      totalRowHomotopy K h n m ≫ totalCoordinate K m q = 0 := by
  classical
  by_cases hm : n + 1 = m
  · subst m
    rw [totalRowHomotopy_succ, ι_totalRowHomotopySucc_assoc,
      Linear.units_smul_comp, Category.assoc, ιTotal_coordinate_ne_outer K _ _ _ _ q hiq,
      comp_zero, smul_zero]
  · simp [totalRowHomotopy, hm]

/-- The horizontal correction is strictly lower triangular on the finite antidiagonal. -/
theorem totalRowHorizontal_lower (h : RowHomotopyData K) (n : ℕ)
    (p q : TotalDegree n) (hpq : p.val.1 ≤ q.val.1) :
    totalSummand K n p ≫ totalRowHorizontal K h n ≫ totalCoordinate K n q = 0 := by
  rcases p with ⟨⟨i, j⟩, hp⟩
  change i + j = n at hp
  subst n
  change K.ιTotal (ComplexShape.down ℕ) i j (i + j) _ ≫ _ ≫ _ = 0
  dsimp only [totalRowHorizontal]
  rw [Preadditive.add_comp, Preadditive.comp_add]
  refine (congrArg₂ (· + ·) ?_ ?_).trans (zero_add (0 :
    (K.X i).X j ⟶ (K.X q.val.1).X q.val.2))
  · rw [← Category.assoc, HomologicalComplex₂.ι_D₁_assoc]
    cases i with
    | zero =>
      rw [HomologicalComplex₂.d₁_eq_zero K _ 0 j _ (by simp), zero_comp, zero_comp]
    | succ i =>
      rw [HomologicalComplex₂.d₁_eq K _ (show (ComplexShape.down ℕ).Rel (i + 1) i
        from rfl) j _ (by
          apply Eq.symm
          apply (ComplexShape.down ℕ).next_eq'
          change i + j + 1 = i + 1 + j
          omega)]
      simp only [Linear.units_smul_comp, Category.assoc]
      rw [ιTotal_totalRowHomotopy_coordinate K h _ _ i j _ q (by
        change i + 1 ≤ q.val.1 at hpq
        omega), comp_zero, smul_zero]
  · rw [show (ComplexShape.down ℕ).prev (i + j) = i + j + 1 from by simp,
      totalRowHomotopy_succ, ← Category.assoc, ι_totalRowHomotopySucc_assoc,
      Linear.units_smul_comp]
    simp only [Category.assoc, Linear.units_smul_comp]
    rw [HomologicalComplex₂.ι_D₁_assoc]
    cases i with
    | zero =>
      rw [HomologicalComplex₂.d₁_eq_zero K _ 0 (j + 1) _ (by simp), zero_comp,
        comp_zero, smul_zero]
    | succ i =>
      rw [HomologicalComplex₂.d₁_eq K _ (show (ComplexShape.down ℕ).Rel (i + 1) i
        from rfl) (j + 1) _ (by change i + (j + 1) = (i + 1) + j; omega)]
      simp only [Linear.units_smul_comp, Category.assoc]
      rw [ιTotal_coordinate_ne_outer K _ i (j + 1) _ q (by
        change i + 1 ≤ q.val.1 at hpq
        omega), comp_zero, smul_zero, comp_zero, smul_zero]

end Quillen.HomologicalAlgebra
