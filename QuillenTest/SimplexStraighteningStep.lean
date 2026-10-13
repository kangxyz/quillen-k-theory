/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Quillen.Topology.Realization.SimplexStraighteningStep

/-! # Independent checks for actual finite simplex straightening adapters -/

open Convexity
open scoped Topology unitInterval

universe u

namespace QuillenTest.SimplexStraightening

open Quillen

variable {Z : Type u} [TopologicalSpace Z]

-- Relative degree two needs only Pi 1 here, never a Pi 2 filling.
example (hs : ∀ z : Z, Subsingleton (HomotopyGroup.Pi 1 Z z))
    (f g : C(StdSimplex ℝ (Fin 2), Z)) (H : C(simplexBoundary 1 × I, Z))
    (hzero : ∀ b : simplexBoundary 1, H (b, 0) = f b.val)
    (hone : ∀ b : simplexBoundary 1, H (b, 1) = g b.val) :
    ∃ K : f.Homotopy g, ∀ (b : simplexBoundary 1) (t : I), K (t, b.val) = H (b, t) :=
  exists_simplex_homotopy_of_boundary 1 hs f g H hzero hone

-- At dimension two there is no vanishing assumption: genuine HEP supplies the endpoint.
example (f : C(StdSimplex ℝ (Fin 3), Z)) (H : C(simplexBoundary 2 × I, Z))
    (hzero : ∀ b : simplexBoundary 2, H (b, 0) = f b.val) :
    ∃ g : C(StdSimplex ℝ (Fin 3), Z), ∃ K : f.Homotopy g,
      ∀ (b : simplexBoundary 2) (t : I), K (t, b.val) = H (b, t) :=
  exists_simplex_homotopy_extension 2 f H hzero

-- A tetrahedral finite chain support has a bounded, literally face-closed family.
example (s : Finset C(StdSimplex ℝ (Fin 4), Z)) :
    (finiteVertexRestrictionClosure s).FaceClosed ∧
      (finiteVertexRestrictionClosure s).Bounded 3 :=
  ⟨finiteVertexRestrictionClosure_faceClosed s, finiteVertexRestrictionClosure_bounded s⟩

-- Equal original maps remain equal after any actual vertex restriction.
example {d e : ℕ} {s τ : C(StdSimplex ℝ (Fin (e + 1)), Z)} (h : s = τ)
    (α : Fin (d + 1) → Fin (e + 1)) :
    singularVertexRestriction s α = singularVertexRestriction τ α :=
  congrArg (fun f ↦ singularVertexRestriction f α) h

-- Membership proof choices never create a second copy of the same singular simplex.
example (d : ℕ) (S : Finset C(StdSimplex ℝ (Fin (d + 1)), Z))
    (s : C(StdSimplex ℝ (Fin (d + 1)), Z)) (h h' : s ∈ S)
    (H : {τ // τ ∈ S} → C(simplexBoundary d × I, Z)) :
    H ⟨s, h⟩ = H ⟨s, h'⟩ := rfl

-- The entire chosen homotopy of an already fixed simplex is stationary.
example (d : ℕ) (z : Z)
    (hs : ∀ x : Z, ∀ k : ℕ, k < d + 1 → Subsingleton (HomotopyGroup.Pi k Z x)) :
    ∃ g : C(StdSimplex ℝ (Fin (d + 1)), Z),
      ∃ K : (ContinuousMap.const _ z).Homotopy g,
        ∀ (t : I) (x : StdSimplex ℝ (Fin (d + 1))), K (t, x) = z := by
  classical
  let f : C(StdSimplex ℝ (Fin (d + 1)), Z) := ContinuousMap.const _ z
  let S : Finset C(StdSimplex ℝ (Fin (d + 1)), Z) := {f}
  let H : {s // s ∈ S} → C(simplexBoundary d × I, Z) := fun _ ↦ ContinuousMap.const _ z
  have heq (s : {s // s ∈ S}) : s.val = f := Finset.mem_singleton.mp s.property
  obtain ⟨g, K, hK⟩ := exists_finite_simplex_straightening_step (d + 1) d z hs S Set.univ H
    (by intro s b; rw [heq]; rfl) (by intros; rfl)
    (by intro s _ b t; rw [heq]; rfl) (by intro s _ _; exact heq s)
  let s : {s // s ∈ S} := ⟨f, Finset.mem_singleton_self f⟩
  exact ⟨g s, K s, fun t x ↦ (hK s).2.2 (Set.mem_univ _) t x⟩

-- In dimension three all four triangular tracks retain their ordinary double-face equations.
example (H : Fin 4 → C(StdSimplex ℝ (Fin 3) × I, Z))
    (hfaces : ∀ (i : Fin 4) (k : Fin 3) (q : StdSimplex ℝ (Fin 2)) (t : I),
      H i (q.map k.succAbove, t) = H (i.succAbove k) (q.map (k.predAbove i).succAbove, t)) :
    ∃ K : C(simplexBoundary 3 × I, Z), ∀ (i : Fin 4) (x : StdSimplex ℝ (Fin 3)) (t : I),
      K (simplexBoundaryFace 2 i x, t) = H i (x, t) :=
  exists_simplex_boundary_track_of_faces 1 H hfaces

end QuillenTest.SimplexStraightening
