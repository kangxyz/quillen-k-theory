/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Algebra.Homology.TotalRowHomotopy

/-!
# Signed vertical cancellation for independently contracted total rows

The two vertical contributions have the same outer-degree sign twice.
They therefore reproduce the original row homotopy boundary on each actual
total summand. No compatibility between distinct row homotopies is needed.
-/

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

/-- The inner total sign depends only on the outer degree. -/
theorem totalRow_inner_sign (i p : ℕ) :
    ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) (i, p) =
      (ComplexShape.down ℕ).ε i := rfl

/-- The contribution of the inner differential to a total row homotopy. -/
def totalRowVertical (h : RowHomotopyData K) (n : ℕ) :
    (K.total (ComplexShape.down ℕ)).X n ⟶ (K.total (ComplexShape.down ℕ)).X n :=
  (show (K.total (ComplexShape.down ℕ)).X n ⟶ (K.total (ComplexShape.down ℕ)).X n from
    K.D₂ (ComplexShape.down ℕ) n ((ComplexShape.down ℕ).next n) ≫
      totalRowHomotopy K h ((ComplexShape.down ℕ).next n) n) +
    (show (K.total (ComplexShape.down ℕ)).X n ⟶ (K.total (ComplexShape.down ℕ)).X n from
      totalRowHomotopy K h n ((ComplexShape.down ℕ).prev n) ≫
        K.D₂ (ComplexShape.down ℕ) ((ComplexShape.down ℕ).prev n) n)

/-- The zero-th inner summand has only its upward-then-downward contribution. -/
@[reassoc]
theorem ι_totalRowVertical_zero (h : RowHomotopyData K) (i : ℕ) :
    K.ιTotal (ComplexShape.down ℕ) i 0 i (Nat.add_zero i) ≫ totalRowVertical K h i =
      h i 0 1 ≫ (K.X i).d 1 0 ≫
        K.ιTotal (ComplexShape.down ℕ) i 0 i (Nat.add_zero i) := by
  rw [totalRowVertical, Preadditive.comp_add, HomologicalComplex₂.ι_D₂_assoc,
    HomologicalComplex₂.d₂_eq_zero K _ i 0 _ (by simp), zero_comp, zero_add]
  rw [ChainComplex.prev ℕ i,
    totalRowHomotopy_succ, ι_totalRowHomotopySucc_assoc,
    Linear.units_smul_comp, Category.assoc, HomologicalComplex₂.ι_D₂,
    HomologicalComplex₂.d₂_eq K _ i (show (ComplexShape.down ℕ).Rel 1 0 from rfl)
      i (Nat.add_zero i)]
  simp only [totalRow_inner_sign, Linear.comp_units_smul, smul_smul,
    Int.units_mul_self, one_smul]

/-- In positive inner degree both contributions are exactly the original row boundary. -/
@[reassoc]
theorem ι_totalRowVertical_succ (h : RowHomotopyData K) (i p : ℕ) :
    K.ιTotal (ComplexShape.down ℕ) i (p + 1) (i + (p + 1)) rfl ≫
        totalRowVertical K h (i + (p + 1)) =
      ((K.X i).d (p + 1) p ≫ h i p (p + 1) +
        h i (p + 1) (p + 2) ≫ (K.X i).d (p + 2) (p + 1)) ≫
          K.ιTotal (ComplexShape.down ℕ) i (p + 1) (i + (p + 1)) rfl := by
  rw [totalRowVertical, Preadditive.comp_add, HomologicalComplex₂.ι_D₂_assoc,
    show (ComplexShape.down ℕ).next (i + (p + 1)) = i + p from
      (ComplexShape.down ℕ).next_eq' (by change i + p + 1 = i + (p + 1); omega),
    ChainComplex.prev ℕ (i + (p + 1)),
    HomologicalComplex₂.d₂_eq K _ i (show (ComplexShape.down ℕ).Rel (p + 1) p from rfl)
      (i + p) rfl]
  have hh : totalRowHomotopy K h (i + p) (i + (p + 1)) =
      totalRowHomotopySucc K h (i + p) := by
    exact totalRowHomotopy_succ K h (i + p)
  rw [hh, totalRowHomotopy_succ, Linear.units_smul_comp, Category.assoc,
    ι_totalRowHomotopySucc, ι_totalRowHomotopySucc_assoc,
    Linear.units_smul_comp, Category.assoc, HomologicalComplex₂.ι_D₂,
    HomologicalComplex₂.d₂_eq K _ i
      (show (ComplexShape.down ℕ).Rel (p + 2) (p + 1) from rfl)
      (i + (p + 1)) rfl]
  simp only [totalRow_inner_sign, Linear.comp_units_smul, smul_smul,
    Int.units_mul_self, one_smul,
    Preadditive.add_comp, Category.assoc]
  rfl

/-- The actual degreewise row projector on the original total summands. -/
def totalRowProjector (r : ∀ i, K.X i ⟶ K.X i) (n : ℕ) :
    (K.total (ComplexShape.down ℕ)).X n ⟶ (K.total (ComplexShape.down ℕ)).X n :=
  K.totalDesc fun i p hip ↦ (r i).f p ≫ K.ιTotal (ComplexShape.down ℕ) i p n hip

@[reassoc (attr := simp)]
theorem ι_totalRowProjector (r : ∀ i, K.X i ⟶ K.X i) (n i p : ℕ) (hip : i + p = n) :
    K.ιTotal (ComplexShape.down ℕ) i p n hip ≫ totalRowProjector K r n =
      (r i).f p ≫ K.ιTotal (ComplexShape.down ℕ) i p n hip := by
  simp [totalRowProjector]

/-- Independent actual row contractions cancel the vertical part of the total differential. -/
theorem totalRowVertical_eq (r : ∀ i, K.X i ⟶ K.X i)
    (h : ∀ i, Homotopy (𝟙 (K.X i)) (r i)) (n : ℕ) :
    totalRowVertical K (fun i ↦ (h i).hom) n = 𝟙 _ - totalRowProjector K r n := by
  apply HomologicalComplex₂.total.hom_ext
  intro i p hip
  change i + p = n at hip
  subst n
  rw [Preadditive.comp_sub, Category.comp_id, ι_totalRowProjector]
  cases p with
  | zero =>
    change K.ιTotal (ComplexShape.down ℕ) i 0 i (Nat.add_zero i) ≫
      totalRowVertical K (fun i ↦ (h i).hom) i = _
    rw [ι_totalRowVertical_zero]
    have hh := (h i).comm 0
    rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, zero_add] at hh
    change 𝟙 _ = (h i).hom 0 1 ≫ (K.X i).d 1 0 + (r i).f 0 at hh
    rw [← Category.assoc, eq_sub_of_add_eq hh.symm, Preadditive.sub_comp, Category.id_comp]
    rfl
  | succ p =>
    rw [ι_totalRowVertical_succ]
    have hh := (h i).comm (p + 1)
    rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at hh
    change 𝟙 _ = (K.X i).d (p + 1) p ≫ (h i).hom p (p + 1) +
      (h i).hom (p + 1) (p + 2) ≫ (K.X i).d (p + 2) (p + 1) + (r i).f (p + 1) at hh
    rw [eq_sub_of_add_eq hh.symm, Preadditive.sub_comp, Category.id_comp]

end Quillen.HomologicalAlgebra
