/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Quillen.Topology.Covering.SingularSimplices

/-! Independent clients of covering-space simplex recovery and simplicial transport. -/

open CategoryTheory Convexity Quillen Quillen.LocalCoefficients
open scoped Simplicial

universe u v

noncomputable section

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
variable {p : E → B} (hp : IsCoveringMap p)

-- Recover the original simplex from its actual projection and original first vertex.
example {n : SimplexCategory} (τ : SingularSimplex E n) :
    Covering.lift hp ((Covering.projection hp).comp τ)
      (τ (StdSimplex.single 0)) rfl = τ :=
  (Covering.eq_lift hp _ _ rfl τ rfl rfl).symm

-- Every prescribed covering fiber point extends to a lift of the entire base simplex.
example {n : SimplexCategory} (σ : SingularSimplex B n)
    (e : E) (he : p e = σ (StdSimplex.single 0)) :
    ∃ τ : SingularSimplex E n,
      (Covering.projection hp).comp τ = σ ∧ τ (StdSimplex.single 0) = e :=
  ⟨Covering.lift hp σ e he, Covering.projection_lift hp σ e he,
    Covering.lift_vertex hp σ e he⟩

-- Degenerate simplices preserve the exact original covering point.
example {n : ℕ} (s : Covering.BasedSimplex p ⦋n⦌) (i : Fin (n + 1)) :
    ((Covering.simplexEquiv hp ⦋n + 1⦌)
      (restrictSimplex ((Covering.simplexEquiv hp ⦋n⦌).symm s)
        (SimplexCategory.σ i))).2.1 = s.2.1 := by
  rw [Covering.simplexEquiv_restrict, Equiv.apply_symm_apply]
  exact Covering.restrict_degeneracy_point hp s i

-- Lift first, restrict twice, and project: the original base composite is recovered.
example {l m n : SimplexCategory} (s : Covering.BasedSimplex p n)
    (α : l ⟶ m) (β : m ⟶ n) :
    (Covering.projection hp).comp
        (restrictSimplex (restrictSimplex ((Covering.simplexEquiv hp n).symm s) β) α) =
      restrictSimplex s.1 (α ≫ β) := by
  rw [← restrictSimplex_comp, ← Covering.lift_restrict]
  exact Covering.projection_lift hp (Covering.restrict hp s (α ≫ β)).1
    (Covering.restrict hp s (α ≫ β)).2.1 (Covering.restrict hp s (α ≫ β)).2.2
