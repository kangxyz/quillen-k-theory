/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.MetricOrderComplex.RealizationCoordinates
public import Mathlib.Data.Finset.Sort
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveNondegenerate

/-!
# Reconstruction on the exact finite chain support

Every metric point is represented by a nondegenerate simplex whose ordered
vertices are exactly its finite support, with strictly positive barycentric
weights. Injective finite-chain charts recover their original weights. In
particular the actual realization coordinate map is surjective. This does
not yet assert a continuous inverse or the global uniqueness of realization
representatives.
-/

@[expose] public section
noncomputable section

open CategoryTheory Convexity Opposite
open scoped Simplicial

universe u v

namespace Quillen.MetricOrderComplex

variable {P : Type u} [PartialOrder P]

/-- An injective chain chart loses no barycentric information. -/
theorem chainCoordinates_injective {ι : Type v} (v : ι → P)
    (hv : IsChain (· ≤ ·) (Set.range v)) (hi : Function.Injective v) :
    Function.Injective (chainCoordinates v hv) := by
  intro t q h
  apply StdSimplex.ext
  exact Finsupp.mapDomain_injective hi (congrArg weights h)

/-- Every metric point has a strictly ordered representative on its exact support. -/
theorem exists_strict_representation (x : MetricOrderComplex P) :
    ∃ (n : ℕ) (s : (nerve P) _⦋n⦌) (t : StdSimplex ℝ (Fin (n + 1))),
      StrictMono s.obj ∧ Set.range s.obj = (x.weights.support : Set P) ∧
      (∀ i, 0 < t.weights i) ∧ simplexCoordinates s t = x := by
  classical
  let S := x.weights.support
  let : LinearOrder S := x.support_chain.lt_of_le.linearOrder
  have hcard : Fintype.card S = (S.card - 1) + 1 := by
    rw [Fintype.card_coe]
    exact (Nat.sub_add_cancel (Finset.card_pos.mpr x.support_nonempty)).symm
  let e : Fin ((S.card - 1) + 1) ≃o S := Fintype.orderIsoFinOfCardEq S hcard
  let v : Fin ((S.card - 1) + 1) → P := fun i ↦ (e i).1
  have hstrict : StrictMono v := e.strictMono
  have hrange : Set.range v = (x.weights.support : Set P) := by
    ext p
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).2
    · intro hp
      exact ⟨e.symm ⟨p, hp⟩, congrArg Subtype.val (e.apply_symm_apply ⟨p, hp⟩)⟩
  obtain ⟨t, ht⟩ : ∃ t : StdSimplex ℝ (Fin ((S.card - 1) + 1)),
      StdSimplex.map v t = x.toStdSimplex := by
    apply (StdSimplex.mem_range_map_iff v x.toStdSimplex).mpr
    intro p hp
    change x.weights p = 0
    exact Finsupp.notMem_support_iff.mp (by simpa only [hrange, Finset.mem_coe] using hp)
  refine ⟨S.card - 1, hstrict.monotone.functor, t, hstrict, hrange, ?_, ?_⟩
  · intro i
    have hi : t.weights i = x.weights (v i) := by
      simpa only [toStdSimplex, weights, StdSimplex.weights_map,
        Finsupp.mapDomain_apply_of_injective hstrict.injective] using
        congrArg (fun q : StdSimplex ℝ P ↦ q.weights (v i)) ht
    rw [hi]
    exact lt_of_le_of_ne (x.weights_nonneg _) (Ne.symm (Finsupp.mem_support_iff.mp (e i).2))
  · exact Subtype.ext ht

/-- The reconstructed simplex is genuinely nondegenerate in the original poset nerve. -/
theorem exists_nondegenerate_representation (x : MetricOrderComplex P) :
    ∃ (n : ℕ) (s : (nerve P) _⦋n⦌) (t : StdSimplex ℝ (Fin (n + 1))),
      s ∈ (nerve P).nonDegenerate n ∧ Set.range s.obj = (x.weights.support : Set P) ∧
      (∀ i, 0 < t.weights i) ∧ realizationCoordinates (realizationSimplex s t) = x := by
  obtain ⟨n, s, t, hs, hr, ht, hx⟩ := exists_strict_representation x
  exact ⟨n, s, t, (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono s).mpr hs,
    hr, ht, (realizationCoordinates_simplex s t).trans hx⟩

/-- The actual coordinate map reaches every finitely supported chain distribution. -/
theorem realizationCoordinates_surjective :
    Function.Surjective (realizationCoordinates (P := P)) := by
  intro x
  obtain ⟨n, s, t, _, _, _, h⟩ := exists_nondegenerate_representation x
  exact ⟨realizationSimplex s t, h⟩

end Quillen.MetricOrderComplex
