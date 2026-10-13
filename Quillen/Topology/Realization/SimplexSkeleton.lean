/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Realization.FiniteSimplexFamily
public import Quillen.Topology.Realization.SimplexFaceGluing
public import Quillen.Topology.HomotopyGroups.SphericalSimplex
public import Mathlib.Data.Fintype.Card

/-!
# Geometric simplex skeleta and spherical fixed families

The `(n - 1)`-skeleton of a standard simplex consists of its points supported
on at most `n` vertices. An injective vertex map preserves the support's
cardinality exactly. Consequently every skeleton point in a sufficiently
large simplex comes from a standard face, and its preimage belongs to the
same skeleton. These are statements about actual geometric points.

A nonsurjective vertex restriction of a spherical simplex is the constant
simplex. In particular all members below the spherical dimension in the
finite vertex-restriction closure are literally constant continuous maps.
-/

@[expose] public section
noncomputable section

open Convexity

universe u

namespace Quillen

/-- The geometric `(n - 1)`-skeleton: points supported on at most `n` vertices. -/
def simplexSkeleton (n d : ℕ) : Set (StdSimplex ℝ (Fin (d + 1))) :=
  {x | x.weights.support.card ≤ n}

@[simp] theorem mem_simplexSkeleton {n d : ℕ}
    (x : StdSimplex ℝ (Fin (d + 1))) :
    x ∈ simplexSkeleton n d ↔ x.weights.support.card ≤ n := Iff.rfl

/-- Below the cutoff, the skeleton is the entire simplex. -/
theorem simplexSkeleton_eq_univ {n d : ℕ} (hd : d < n) :
    simplexSkeleton n d = Set.univ := by
  ext x
  simp only [Set.mem_univ, iff_true, mem_simplexSkeleton]
  have hc : x.weights.support.card ≤ d + 1 := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ x.weights.support
  exact hc.trans (by omega)

/-- The empty skeleton has no geometric points, including in dimension zero. -/
@[simp] theorem simplexSkeleton_zero (d : ℕ) : simplexSkeleton 0 d = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false, mem_simplexSkeleton]
  have hc := Finset.card_pos.mpr x.support_weights_nonempty
  omega

/-- Injective vertex maps preserve the number of nonzero barycentric coordinates. -/
theorem simplex_map_support_card_of_injective {A B : Type*} (α : A → B)
    (hα : Function.Injective α) (x : StdSimplex ℝ A) :
    (x.map α).weights.support.card = x.weights.support.card := by
  let e : A ↪ B := ⟨α, hα⟩
  change (Finsupp.mapDomain e x.weights).support.card = x.weights.support.card
  rw [Finsupp.support_mapDomain_embedding, Finset.card_map]

/-- A point and its image under an injective vertex map lie in the same skeleton. -/
theorem simplex_map_mem_skeleton_iff {n d e : ℕ}
    (α : Fin (d + 1) → Fin (e + 1)) (hα : Function.Injective α)
    (x : StdSimplex ℝ (Fin (d + 1))) :
    x.map α ∈ simplexSkeleton n e ↔ x ∈ simplexSkeleton n d := by
  simp only [mem_simplexSkeleton, simplex_map_support_card_of_injective α hα]

/-- A skeleton point above the cutoff has a zero barycentric coordinate. -/
theorem simplexSkeleton_subset_boundary {n d : ℕ} (hnd : n ≤ d) :
    simplexSkeleton n d ⊆ simplexBoundary d := by
  intro x hx
  change x.weights.support.card ≤ n at hx
  change ∃ i, x.weights i = 0
  by_contra hzero
  have hs : x.weights.support = Finset.univ := by
    ext i
    simp only [Finset.mem_univ, iff_true]
    exact Finsupp.mem_support_iff.mpr (fun hi ↦ hzero ⟨i, hi⟩)
  rw [hs, Finset.card_univ, Fintype.card_fin] at hx
  omega

/-- Every skeleton point in a simplex above the cutoff lifts to one standard
face, and the lift retains the same support bound. -/
theorem simplexSkeleton_face_preimage {n d : ℕ} (hnd : n ≤ d + 1)
    (x : StdSimplex ℝ (Fin (d + 2))) (hx : x ∈ simplexSkeleton n (d + 1)) :
    ∃ (i : Fin (d + 2)) (y : StdSimplex ℝ (Fin (d + 1))),
      y ∈ simplexSkeleton n d ∧ y.map i.succAbove = x := by
  obtain ⟨i, hi⟩ := simplexSkeleton_subset_boundary hnd hx
  have hxrange : x ∈ Set.range (StdSimplex.map i.succAbove) := by
    rw [StdSimplex.mem_range_map_iff]
    intro j hj
    have hji : j = i := by simpa [Fin.range_succAbove] using hj
    simpa only [hji] using hi
  obtain ⟨y, hy⟩ := hxrange
  refine ⟨i, y, ?_, hy⟩
  apply (simplex_map_mem_skeleton_iff i.succAbove Fin.succAbove_right_injective y).mp
  simpa only [hy] using hx

variable {Z : Type u} [TopologicalSpace Z] {z : Z}

/-- A nonsurjective vertex restriction of a spherical simplex is literally
constant, since every image point lies in the geometric boundary. -/
theorem singularVertexRestriction_eq_const_of_not_surjective {n d : ℕ}
    (σ : SphericalSimplex Z z n) (α : Fin (d + 1) → Fin (n + 1))
    (hα : ¬ Function.Surjective α) :
    singularVertexRestriction σ.val α = ContinuousMap.const _ z := by
  ext x
  change σ (x.map α) = z
  apply σ.boundary
  obtain ⟨i, hi⟩ := not_forall.mp hα
  exact ⟨i, (StdSimplex.mem_range_map_iff α _).mp ⟨x, rfl⟩ i hi⟩

/-- Lower-dimensional vertex restrictions of a spherical simplex are constant. -/
theorem SphericalSimplex.singularVertexRestriction_eq_const {n d : ℕ}
    (σ : SphericalSimplex Z z n) (hd : d < n)
    (α : Fin (d + 1) → Fin (n + 1)) :
    singularVertexRestriction σ.val α = ContinuousMap.const _ z := by
  apply singularVertexRestriction_eq_const_of_not_surjective σ α
  intro hα
  have hc := Fintype.card_le_of_surjective α hα
  simp only [Fintype.card_fin] at hc
  omega

/-- Every low-dimensional member of the finite fixed family generated by a
spherical simplex is the constant singular simplex. -/
theorem SphericalSimplex.finiteVertexRestrictionClosure_eq_const {n d : ℕ}
    (σ : SphericalSimplex Z z n) (hd : d < n)
    {τ : C(StdSimplex ℝ (Fin (d + 1)), Z)}
    (hτ : τ ∈ finiteVertexRestrictionClosure {σ.val} d) :
    τ = ContinuousMap.const _ z := by
  classical
  obtain ⟨_, ρ, hρ, α, rfl⟩ :=
    (mem_finiteVertexRestrictionClosure {σ.val} τ).mp hτ
  have hρeq : ρ = σ.val := Finset.mem_singleton.mp hρ
  subst ρ
  exact σ.singularVertexRestriction_eq_const hd α

/-- Below its dimension, the generated spherical fixed family has exactly one
actual member, namely the constant map. -/
theorem SphericalSimplex.finiteVertexRestrictionClosure_eq_singleton {n d : ℕ}
    (σ : SphericalSimplex Z z n) (hd : d < n) :
    finiteVertexRestrictionClosure {σ.val} d = {ContinuousMap.const _ z} := by
  classical
  ext τ
  constructor
  · intro hτ
    exact Finset.mem_singleton.mpr (σ.finiteVertexRestrictionClosure_eq_const hd hτ)
  · intro hτ
    have hτeq : τ = ContinuousMap.const _ z := Finset.mem_singleton.mp hτ
    subst τ
    rw [mem_finiteVertexRestrictionClosure]
    exact ⟨by omega, σ.val, Finset.mem_singleton_self _, fun _ ↦ 0,
      σ.singularVertexRestriction_eq_const hd (fun _ ↦ 0)⟩

end Quillen
