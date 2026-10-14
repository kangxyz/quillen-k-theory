/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1MergedComponentNative

/-! Exact support coverage of the four fixed old62 scalar faces in the enlarged actual family. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory Convexity Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassH1Support

/-- The original positive chart remains in its three actual retained old62 faces. -/
theorem old_plus_support (z : unitInterval × unitInterval) :
    ∃ (i : Fin 3) (y : StdSimplex ℝ (Fin 8)),
      StdSimplex.map (BassSupportOrder.oldPlusFace i).toOrderHom y =
        BassSupportOrder.plusParameter z := by
  obtain ⟨i, y, hy⟩ := BassPrimitiveSupport.plus_chart_support z
  refine ⟨i, y, ?_⟩
  change _ = StdSimplex.map BassSupportOrder.oldIndex (BassReferenceMerge.plusParameter z)
  rw [← hy]
  exact StdSimplex.map_comp y
    ((BassPrimitiveSupport.rectangleFace i ≫ BassOverlap.plusFace) ≫
      BassReferenceMerge.chartFace).toOrderHom BassSupportOrder.oldIndex

/-- The original inverse chart retains its own three actual old62 faces. -/
theorem old_minus_support (z : unitInterval × unitInterval) :
    ∃ (i : Fin 3) (y : StdSimplex ℝ (Fin 8)),
      StdSimplex.map (BassSupportOrder.oldMinusFace i).toOrderHom y =
        BassSupportOrder.minusParameter z := by
  obtain ⟨i, y, hy⟩ := BassPrimitiveSupport.minus_chart_support z
  refine ⟨i, y, ?_⟩
  change _ = StdSimplex.map BassSupportOrder.oldIndex (BassReferenceMerge.minusParameter z)
  rw [← hy]
  exact StdSimplex.map_comp y
    ((BassPrimitiveSupport.rectangleFace i ≫ BassOverlap.minusFace) ≫
      BassReferenceMerge.chartFace).toOrderHom BassSupportOrder.oldIndex

/-- The full original bottom product remains in its exact retained old62 fourteen-face. -/
theorem old_bottom_support (z : unitInterval × unitInterval) :
    ∃ y : StdSimplex ℝ (Fin 15),
      StdSimplex.map BassSupportOrder.bottomFace.toOrderHom y =
        BassSupportOrder.bottomParameter.{u} z := by
  refine ⟨BassLaurentBottomFace.parameter.{u} z, ?_⟩
  change _ = StdSimplex.map BassSupportOrder.oldIndex
    (StdSimplex.map BassReferenceMerge.bottomFace.toOrderHom
      (BassLaurentBottomFace.parameter.{u} z))
  exact StdSimplex.map_comp (BassLaurentBottomFace.parameter.{u} z)
    BassReferenceMerge.bottomFace.toOrderHom BassSupportOrder.oldIndex

/-- Every original H0 value retains one of the six original full triple support faces. -/
theorem old_h0_support (z : unitInterval × unitInterval) :
    (∃ (i : Fin 3) (y : StdSimplex ℝ (Fin 8)),
      StdSimplex.map (BassSupportOrder.h0PlusFace i).toOrderHom y =
        BassSupportOrder.h0Parameter z) ∨
    (∃ (i : Fin 3) (y : StdSimplex ℝ (Fin 8)),
      StdSimplex.map (BassSupportOrder.h0MinusFace i).toOrderHom y =
        BassSupportOrder.h0Parameter z) := by
  obtain ⟨α, hα, i, y, hy⟩ := BassPrimitiveSupport.h0_support z
  rcases Set.mem_insert_iff.mp hα with hα | hα
  · subst α
    refine Or.inl ⟨i, y, ?_⟩
    change _ = StdSimplex.map BassSupportOrder.h0Index (BassH0Diagram.parameter z)
    rw [← hy]
    exact StdSimplex.map_comp y
      (BassPrimitiveSupport.rectangleFace i ≫ BassH0Diagram.plusFace).toOrderHom
      BassSupportOrder.h0Index
  · have hα' := Set.mem_singleton_iff.mp hα
    subst α
    refine Or.inr ⟨i, y, ?_⟩
    change _ = StdSimplex.map BassSupportOrder.h0Index (BassH0Diagram.parameter z)
    rw [← hy]
    exact StdSimplex.map_comp y
      (BassPrimitiveSupport.rectangleFace i ≫ BassH0Diagram.minusFace).toOrderHom
      BassSupportOrder.h0Index

end Quillen.PerfectComplexes.BassH1Support
