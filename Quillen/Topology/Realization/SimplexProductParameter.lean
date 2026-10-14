/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.Topology.Realization.ProductSimplex

/-! The actual realization of the monotone grid inclusion provides a product parameter.
No coordinate-product formula is assumed. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory MonoidalCategory CartesianMonoidalCategory Convexity Opposite
open scoped Simplicial Topology
universe u
namespace Quillen.SimplexGrid

/-- Dimension of the simplex with one vertex for every ordered pair of grid vertices. -/
def dimension (p q : ℕ) : ℕ := p * (q + 1) + q

/-- A monotone lexicographic enumeration of the product grid. -/
def index (p q : ℕ) : Fin (p + 1) × Fin (q + 1) →o Fin (dimension p q + 1) where
  toFun z := ⟨z.1.val * (q + 1) + z.2.val, by
    have hi := Nat.le_of_lt_succ z.1.isLt
    have hj := z.2.isLt
    have h := Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul_right (q + 1) hi) hj
    simpa only [dimension, Nat.add_assoc] using h⟩
  monotone' _ _ h := Nat.add_le_add (Nat.mul_le_mul_right (q + 1) h.1) h.2


/-- The grid enumeration is a bijection of vertex sets; its inverse is used only on vertices. -/
def indexEquiv (p q : ℕ) :
    Fin (p + 1) × Fin (q + 1) ≃ Fin (dimension p q + 1) :=
  finProdFinEquiv.trans (finCongr (by simp [dimension, Nat.add_mul, Nat.add_assoc]))

theorem index_eq_equiv (p q : ℕ) (z : Fin (p + 1) × Fin (q + 1)) :
    index p q z = indexEquiv p q z := by
  apply Fin.ext
  change z.1.val * (q + 1) + z.2.val = z.2.val + (q + 1) * z.1.val
  ac_rfl

@[simp] theorem decode_index (p q : ℕ) (z : Fin (p + 1) × Fin (q + 1)) :
    (indexEquiv p q).symm (index p q z) = z := by
  rw [index_eq_equiv, Equiv.symm_apply_apply]

/-- Literal simplicial grid embedding into its linearly ordered common vertex set. -/
def embedding (p q : ℕ) : (Δ[p] ⊗ Δ[q] : SSet.{u}) ⟶ Δ[dimension p q] where
  app n := ↾fun z ↦ SSet.stdSimplex.objMk
    ((index p q).comp (SSet.prodStdSimplex.objEquiv z))
  naturality _ _ _ := by
    ext z : 4
    rfl

/-- The product parameter uses the actual inverse realization product homeomorphism. -/
def parameter (p q : ℕ) :
    C(StdSimplex ℝ (Fin (p + 1)) × StdSimplex ℝ (Fin (q + 1)),
      StdSimplex ℝ (Fin (dimension p q + 1))) :=
  ⟨fun z ↦ SimplexCategory.toTopHomeo.{u} ⦋dimension p q⦌
    (SSet.toTop.map (embedding p q) ((realizationProductSimplexHomeomorph p q).symm z)),
    by fun_prop⟩

/-- Retain the whole original realization coordinate when entering the common simplex. -/
theorem parameter_realization (p q : ℕ) (z : |(Δ[p] ⊗ Δ[q] : SSet.{u})|) :
    parameter.{u} p q (realizationProductSimplexHomeomorph p q z) =
      SimplexCategory.toTopHomeo.{u} ⦋dimension p q⦌ (SSet.toTop.map (embedding p q) z) := by
  change SimplexCategory.toTopHomeo _
    (SSet.toTop.map (embedding p q)
      ((realizationProductSimplexHomeomorph p q).symm
        (realizationProductSimplexHomeomorph p q z))) = _
  rw [Homeomorph.symm_apply_apply]

end Quillen.SimplexGrid
