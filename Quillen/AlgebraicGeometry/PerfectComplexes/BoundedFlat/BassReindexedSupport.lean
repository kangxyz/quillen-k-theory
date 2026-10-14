/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassReindexedScalarEdges

/-! Every reindexed original surface value lies in one of the thirteen retained ordered faces. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory Convexity Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassSupportOrder

/-- The positive chart is covered by its three original whole split-triple faces. -/
theorem plus_support (z : unitInterval × unitInterval) :
    ∃ i : Fin 3, ∃ y : StdSimplex ℝ (Fin 8), embed (oldPlusFace i) y = plusParameter z := by
  obtain ⟨i, y, hy⟩ := BassPrimitiveSupport.plus_chart_support z
  refine ⟨i, y, ?_⟩
  have he := congrArg (StdSimplex.map oldIndex) hy
  change StdSimplex.map oldIndex (StdSimplex.map _ y) = plusParameter z at he
  rw [← StdSimplex.map_comp] at he
  exact he

/-- The inverse chart is independently covered by its own three original triple faces. -/
theorem minus_support (z : unitInterval × unitInterval) :
    ∃ i : Fin 3, ∃ y : StdSimplex ℝ (Fin 8), embed (oldMinusFace i) y = minusParameter z := by
  obtain ⟨i, y, hy⟩ := BassPrimitiveSupport.minus_chart_support z
  refine ⟨i, y, ?_⟩
  have he := congrArg (StdSimplex.map oldIndex) hy
  change StdSimplex.map oldIndex (StdSimplex.map _ y) = minusParameter z at he
  rw [← StdSimplex.map_comp] at he
  exact he

/-- The whole original realized-product bottom stays in its retained fourteen-face. -/
theorem bottom_support (z : unitInterval × unitInterval) :
    ∃ y : StdSimplex ℝ (Fin 15), embed bottomFace y = bottomParameter.{u} z := by
  refine ⟨BassLaurentBottomFace.parameter z, ?_⟩
  change StdSimplex.map (oldIndex ∘ BassReferenceMerge.bottomFace.toOrderHom) _ =
    StdSimplex.map oldIndex (StdSimplex.map BassReferenceMerge.bottomFace.toOrderHom _)
  rw [StdSimplex.map_comp]

/-- The entire original pasted H0 family is covered by its six ordered original triple faces. -/
theorem h0_support (z : unitInterval × unitInterval) :
    (∃ i : Fin 3, ∃ y : StdSimplex ℝ (Fin 8), embed (h0PlusFace i) y = h0Parameter z) ∨
    (∃ i : Fin 3, ∃ y : StdSimplex ℝ (Fin 8), embed (h0MinusFace i) y = h0Parameter z) := by
  obtain ⟨α, hα, i, y, hy⟩ := BassPrimitiveSupport.h0_support z
  have he := congrArg (StdSimplex.map h0Index) hy
  change StdSimplex.map h0Index (StdSimplex.map _ y) = h0Parameter z at he
  rw [← StdSimplex.map_comp] at he
  rcases Set.mem_insert_iff.mp hα with hα | hα
  · subst α
    exact Or.inl ⟨i, y, he⟩
  · have hα' := Set.mem_singleton_iff.mp hα
    subst α
    exact Or.inr ⟨i, y, he⟩

end Quillen.PerfectComplexes.BassSupportOrder
