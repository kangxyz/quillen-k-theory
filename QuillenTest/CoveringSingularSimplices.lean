/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Quillen.Topology.Covering.SingularSimplices

/-!
# Clients of actual covering-simplex lifting

These consumers test uniqueness of a lifted triangular face, compositional
restriction on transported fiber data, and naturality in a commuting square
whose four spaces have independent universes.
-/

open CategoryTheory Convexity Quillen Quillen.LocalCoefficients
open scoped Simplicial

universe u v w z

noncomputable section

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
variable {p : E → B} (hp : IsCoveringMap p)

-- Agreement of projections and a single vertex determines the entire simplex.
example {n : SimplexCategory} (τ τ' : SingularSimplex E n)
    (h : (Covering.projection hp).comp τ = (Covering.projection hp).comp τ')
    (h₀ : τ (StdSimplex.single 0) = τ' (StdSimplex.single 0)) : τ = τ' := by
  have hτ := Covering.eq_lift hp ((Covering.projection hp).comp τ')
    (τ' (StdSimplex.single 0)) rfl τ h h₀
  have hτ' := Covering.eq_lift hp ((Covering.projection hp).comp τ')
    (τ' (StdSimplex.single 0)) rfl τ' rfl rfl
  exact hτ.trans hτ'.symm

-- The first triangular face starts at the monodromy transport to vertex one.
example (σ : SingularSimplex B ⦋2⦌) (e : E)
    (he : p e = σ (StdSimplex.single 0)) :
    restrictSimplex (Covering.lift hp σ e he) (SimplexCategory.δ 0)
        (StdSimplex.single 0) =
      (Covering.simplexTransport hp σ (StdSimplex.single 0)
        (StdSimplex.single 1) ⟨e, he⟩).1 := by
  rw [restrictSimplex_firstFace_vertex]
  exact (Covering.simplexTransport_lift hp σ e he (StdSimplex.single 1)).symm

-- Restriction and its monodromy data really satisfy the simplicial composition law.
example {l m n : SimplexCategory} (s : Covering.BasedSimplex p n)
    (α : l ⟶ m) (β : m ⟶ n) :
    (Covering.simplexEquiv hp l).symm
        (Covering.restrict hp (Covering.restrict hp s β) α) =
      restrictSimplex ((Covering.simplexEquiv hp n).symm s) (α ≫ β) := by
  rw [← Covering.restrict_comp, Covering.lift_restrict]

-- A map between coverings need not itself be a covering map.
example {E' : Type w} {B' : Type z} [TopologicalSpace E'] [TopologicalSpace B']
    {p' : E' → B'} (hp' : IsCoveringMap p') (k : C(E, E')) (f : C(B, B'))
    (h : ∀ e, p' (k e) = f (p e)) {n : SimplexCategory}
    (σ : SingularSimplex B n) (e : E) (he : p e = σ (StdSimplex.single 0)) :
    (Covering.projection hp').comp (k.comp (Covering.lift hp σ e he)) = f.comp σ := by
  rw [Covering.map_lift hp hp' k f h σ e he, Covering.projection_lift]

-- This is valid in dimension zero and does not assume surjectivity of the cover.
example (σ : SingularSimplex B ⦋0⦌)
    (h : ∀ e : E, p e ≠ σ (StdSimplex.single 0)) :
    ¬∃ τ : SingularSimplex E ⦋0⦌, (Covering.projection hp).comp τ = σ := by
  rintro ⟨τ, hτ⟩
  exact h (τ (StdSimplex.single 0)) (ContinuousMap.congr_fun hτ _)
