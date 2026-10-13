/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Algebra.Homology.TotalComplexCoordinates

/-! # Finite triangular operators on the actual first-quadrant total complex -/

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

/-- An element supported strictly below an outer-degree bound. -/
def TotalBelow (n r : ℕ) (x : (K.total (ComplexShape.down ℕ)).X n) : Prop :=
  ∀ p : TotalDegree n, r ≤ p.val.1 → totalCoordinate K n p x = 0

/-- There are no summands beyond the finite first-quadrant antidiagonal. -/
theorem totalBelow_all (n : ℕ) (x : (K.total (ComplexShape.down ℕ)).X n) :
    TotalBelow K n (n + 1) x := by
  intro p hp
  have hp' : p.val.1 + p.val.2 = n := p.property
  omega

/-- Support below zero means the actual total element is zero. -/
theorem totalBelow_zero (n : ℕ) (x : (K.total (ComplexShape.down ℕ)).X n)
    (hx : TotalBelow K n 0 x) : x = 0 := by
  apply totalCoordinate_ext K n
  intro p
  rw [map_zero]
  exact hx p (Nat.zero_le _)

/-- A strictly lower triangular operator lowers the finite outer support. -/
theorem totalBelow_map (n : ℕ)
    (q : (K.total (ComplexShape.down ℕ)).X n ⟶ (K.total (ComplexShape.down ℕ)).X n)
    (hq : ∀ p t : TotalDegree n, p.val.1 ≤ t.val.1 →
      totalSummand K n p ≫ q ≫ totalCoordinate K n t = 0)
    (r : ℕ) (x : (K.total (ComplexShape.down ℕ)).X n)
    (hx : TotalBelow K n (r + 1) x) : TotalBelow K n r (q x) := by
  classical
  intro t ht
  have hrec := congrArg (fun a ↦ a x) (totalCoordinate_sum K n)
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.comp_apply,
    ModuleCat.id_apply] at hrec
  rw [← hrec, map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro p _
  by_cases hp : r + 1 ≤ p.val.1
  · rw [hx p hp, map_zero, map_zero, map_zero]
  · have hpt : p.val.1 ≤ t.val.1 := by omega
    have heq := congrArg (fun a ↦ a (totalCoordinate K n p x)) (hq p t hpt)
    exact heq

variable {K} {L : ChainComplex (ModuleCat.{u} ℤ) ℕ}
  (f : K.total (ComplexShape.down ℕ) ⟶ L)
  (t : K.total (ComplexShape.down ℕ) ⟶ K.total (ComplexShape.down ℕ))

/-- Iteration of the actual chain endomorphism. -/
def totalIterate : ℕ → (K.total (ComplexShape.down ℕ) ⟶ K.total (ComplexShape.down ℕ))
  | 0 => 𝟙 _
  | k + 1 => t ≫ totalIterate k

@[simp]
theorem totalIterate_zero : totalIterate t 0 = 𝟙 _ := rfl

@[simp]
theorem totalIterate_succ (k : ℕ) : totalIterate t (k + 1) = t ≫ totalIterate t k := rfl

/-- A triangular defect of a degreewise section vanishes eventually on the actual kernel. -/
theorem totalIterate_eventually_zero
    (s : ∀ n, L.X n ⟶ (K.total (ComplexShape.down ℕ)).X n)
    (hcomm : t ≫ f = f)
    (hlower : ∀ n (p q : TotalDegree n), p.val.1 ≤ q.val.1 →
      totalSummand K n p ≫ (t.f n - f.f n ≫ s n) ≫ totalCoordinate K n q = 0)
    (n : ℕ) (x : (K.total (ComplexShape.down ℕ)).X n) (hx : f.f n x = 0) :
    ∃ k, (totalIterate t k).f n x = 0 := by
  have main : ∀ r (y : (K.total (ComplexShape.down ℕ)).X n),
      TotalBelow K n r y → f.f n y = 0 →
      ∃ k, (totalIterate t k).f n y = 0 := by
    intro r
    induction r with
    | zero =>
      intro y hy _
      refine ⟨0, ?_⟩
      exact totalBelow_zero K n y hy
    | succ r ih =>
      intro y hy hfy
      have heq : (t.f n - f.f n ≫ s n) y = t.f n y := by
        simp [hfy]
      have hbelow : TotalBelow K n r (t.f n y) := by
        rw [← heq]
        exact totalBelow_map K n _ (hlower n) r y hy
      have hker : f.f n (t.f n y) = 0 := by
        have hc := congrArg (fun a ↦ a.f n y) hcomm
        exact hc.trans hfy
      obtain ⟨k, hk⟩ := ih (t.f n y) hbelow hker
      exact ⟨k + 1, hk⟩
  exact main (n + 1) x (totalBelow_all K n x) hx

end Quillen.HomologicalAlgebra
