/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.Topology.Path.ParameterBoundarySupport
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassMergedScalarBoundary

/-! Actual support coverage for the unchanged chart, bottom, and H0 scalar families. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory Convexity Quillen.SimplexParameters Quillen.ParameterSupport
open scoped Simplicial Topology unitInterval
namespace Quillen.PerfectComplexes.BassPrimitiveSupport

/-- The three original full split-triple faces of one native rectangle. -/
def rectangleFace : Fin 3 → (⦋7⦌ ⟶ ⦋17⦌) :=
  ![DoubleSquareMergedSimplex.firstFace, DoubleSquareMergedSimplex.middleFace,
    DoubleSquareMergedSimplex.lastFace]

/-- Only the three actual seven-simplices are retained, with no claim about the other points. -/
def rectangleSupport : Set (StdSimplex ℝ (Fin 18)) :=
  {z | ∃ i : Fin 3, ∃ y : StdSimplex ℝ (Fin 8), embed (rectangleFace i) y = z}

theorem first_in : HomotopyIn rectangleSupport DoubleSquareScalarPaths.firstComparison :=
  fun z ↦ ⟨0, SplitTripleSimplex.comparisonParameter z, rfl⟩

theorem middle_in : HomotopyIn rectangleSupport DoubleSquareScalarPaths.middleComparison :=
  fun z ↦ ⟨1, SplitTripleSimplex.comparisonParameter z, rfl⟩

theorem last_in : HomotopyIn rectangleSupport DoubleSquareScalarPaths.lastComparison :=
  fun z ↦ ⟨2, SplitTripleSimplex.comparisonParameter z, rfl⟩

/-- Every value of the exact native rectangle factors through one original full triple face. -/
theorem rectangle_in : HomotopyIn rectangleSupport DoubleSquareScalarPaths.rectangleParameter :=
  threeRoutes_in first_in middle_in last_in

theorem original_comparison_in :
    HomotopyIn rectangleSupport DoubleSquareScalarPaths.originalComparisonParameter :=
  hom_cast (hom_symm₂ rectangle_in) _ _

theorem coefficient_boundary_in :
    HomotopyIn rectangleSupport DoubleSquareScalarPaths.coefficientBoundaryParameter :=
  boundaryOfComparison_in original_comparison_in

/-- All original reversals, cancellation speeds, terminal pause, and collapse retain the support. -/
theorem paused_chart_in (z : unitInterval × unitInterval) :
    DoubleSquareScalarPaths.coefficientPausedSquareParameter z ∈ rectangleSupport :=
  collapsed_in (pauseRight_in coefficient_boundary_in) z

/-- Face embeddings compose literally on scalar values. -/
theorem embed_comp {i j k : ℕ} (α : ⦋i⦌ ⟶ ⦋j⦌) (β : ⦋j⦌ ⟶ ⦋k⦌)
    (z : StdSimplex ℝ (Fin (i + 1))) : embed β (embed α z) = embed (α ≫ β) z := by
  change StdSimplex.map β.toOrderHom (StdSimplex.map α.toOrderHom z) = _
  rw [← StdSimplex.map_comp]
  rfl

/-- An actual support point stays on the same primitive face after its enclosing face is mapped. -/
theorem map_supported {k : ℕ} (α : ⦋17⦌ ⟶ ⦋k⦌) {z : StdSimplex ℝ (Fin 18)}
    (hz : z ∈ rectangleSupport) :
    ∃ i : Fin 3, ∃ y : StdSimplex ℝ (Fin 8), embed (rectangleFace i ≫ α) y = embed α z := by
  obtain ⟨i, y, rfl⟩ := hz
  exact ⟨i, y, (embed_comp _ _ _).symm⟩

/-- Every point of the entire original positive chart lies on one of its three retained triples. -/
theorem plus_chart_support (z : unitInterval × unitInterval) :
    ∃ i : Fin 3, ∃ y : StdSimplex ℝ (Fin 8),
      embed ((rectangleFace i ≫ BassOverlap.plusFace) ≫ BassReferenceMerge.chartFace) y =
        BassReferenceMerge.plusParameter z := by
  obtain ⟨i, y, hy⟩ := map_supported
    (BassOverlap.plusFace ≫ BassReferenceMerge.chartFace) (paused_chart_in z)
  refine ⟨i, y, ?_⟩
  rw [Category.assoc]
  exact hy.trans (embed_comp _ _ _).symm

/-- The separate inverse chart retains its own three full original triples. -/
theorem minus_chart_support (z : unitInterval × unitInterval) :
    ∃ i : Fin 3, ∃ y : StdSimplex ℝ (Fin 8),
      embed ((rectangleFace i ≫ BassOverlap.minusFace) ≫ BassReferenceMerge.chartFace) y =
        BassReferenceMerge.minusParameter z := by
  obtain ⟨i, y, hy⟩ := map_supported
    (BassOverlap.minusFace ≫ BassReferenceMerge.chartFace) (paused_chart_in z)
  refine ⟨i, y, ?_⟩
  rw [Category.assoc]
  exact hy.trans (embed_comp _ _ _).symm

/-- The full original bottom already factors through its retained fourteen-simplex. -/
theorem bottom_support (z : unitInterval × unitInterval) :
    ∃ y : StdSimplex ℝ (Fin 15),
      embed BassReferenceMerge.bottomFace y = BassReferenceMerge.bottomParameter z :=
  ⟨BassLaurentBottomFace.parameter z, rfl⟩

/-- The six primitive supports of the original H0 projection pasting. -/
def h0Support : Set (StdSimplex ℝ (Fin 31)) :=
  (embed BassH0Diagram.plusFace) '' rectangleSupport ∪
    (embed BassH0Diagram.minusFace) '' rectangleSupport

theorem h0_plus_in : HomotopyIn h0Support
    (ProjectionRectangleParameters.rectangle BassH0Diagram.plusFace) :=
  fun z ↦ Or.inl ⟨DoubleSquareScalarPaths.rectangleParameter z, rectangle_in z, rfl⟩

theorem h0_minus_in : HomotopyIn h0Support
    (ProjectionRectangleParameters.rectangle BassH0Diagram.minusFace) :=
  fun z ↦ Or.inr ⟨DoubleSquareScalarPaths.rectangleParameter z, rectangle_in z, rfl⟩

/-- The whole original H0 surface stays in the six triple supports through its native paste. -/
theorem h0_in (z : unitInterval × unitInterval) : BassH0Diagram.parameter z ∈ h0Support :=
  collapsed_in (pasteProjectionSquares_in h0_plus_in h0_minus_in) z

/-- Explicit primitive-face factorization of every original H0 scalar value. -/
theorem h0_support (z : unitInterval × unitInterval) :
    ∃ α ∈ ({BassH0Diagram.plusFace, BassH0Diagram.minusFace} : Set (⦋17⦌ ⟶ ⦋30⦌)),
      ∃ i : Fin 3, ∃ y : StdSimplex ℝ (Fin 8),
        embed (rectangleFace i ≫ α) y = BassH0Diagram.parameter z := by
  rcases h0_in z with ⟨w, hw, he⟩ | ⟨w, hw, he⟩
  · obtain ⟨i, y, hy⟩ := map_supported BassH0Diagram.plusFace hw
    exact ⟨_, Set.mem_insert _ _, i, y, hy.trans he⟩
  · obtain ⟨i, y, hy⟩ := map_supported BassH0Diagram.minusFace hw
    exact ⟨_, Set.mem_insert_of_mem _ (Set.mem_singleton _), i, y, hy.trans he⟩

end Quillen.PerfectComplexes.BassPrimitiveSupport
