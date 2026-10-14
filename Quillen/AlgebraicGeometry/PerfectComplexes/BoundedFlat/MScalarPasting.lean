/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MChartSideScalars

/-! Literal scalar pasting from the finite index equations of the actual proved boundary nodes. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Convexity Quillen.SimplexParameters Quillen.NativePathCells Quillen.ScalarRectangle
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMScalarPasting
open BassMOuterJoin
variable {k : ℕ} (f : Fin 45 → Fin (k + 1)) (g : Fin 131 → Fin (k + 1))

/-- Finite label equalities, all supplied by the concrete common-order certificate. -/
structure IndexEqualities : Prop where
  sourcePlus : ∀ i, f (sourcePlusIndex i) = g (oldSourcePlusIndex i)
  sourceMiddle : ∀ i, f (sourceMiddleIndex i) = g (oldSourceMiddleIndex i)
  sourceMinus : ∀ i, f (sourceMinusIndex i) = g (oldSourceMinusIndex i)
  sidePlus : ∀ i, f (sidePlusIndex i) = g (oldSidePlusIndex i)
  sideMinus : ∀ i, f (sideMinusIndex i) = g (oldSideMinusIndex i)
  firstPlus : ∀ i, f (targetFirstPlusIndex i) = g (oldTargetFirstPlusIndex i)
  secondPlus : ∀ i, f (targetSecondPlusIndex i) = g (oldTargetSecondPlusIndex i)
  middle : ∀ i, f (targetMiddleIndex i) = g (oldTargetMiddleIndex i)
  secondMinus : ∀ i, f (targetSecondMinusIndex i) = g (oldTargetSecondMinusIndex i)
  firstMinus : ∀ i, f (targetFirstMinusIndex i) = g (oldTargetFirstMinusIndex i)

/-- Equal finite labels preserve every barycentric value, with no monotonicity premise here. -/
theorem map_index_values {d : ℕ} (a : Fin (d + 1) → Fin 45) (b : Fin (d + 1) → Fin 131)
    (h : ∀ i, f (a i) = g (b i)) (z : StdSimplex ℝ (Fin (d + 1))) :
    StdSimplex.map f (StdSimplex.map a z) = StdSimplex.map g (StdSimplex.map b z) := by
  rw [← StdSimplex.map_comp, ← StdSimplex.map_comp]
  exact congrArg (fun h : Fin (d + 1) → Fin (k + 1) ↦ StdSimplex.map h z) (funext h)

def h0 : C(unitInterval × unitInterval, StdSimplex ℝ (Fin (k + 1))) :=
  ⟨fun z ↦ StdSimplex.map g (BassH1Order.h0Parameter z), by fun_prop⟩
def h1 : C(unitInterval × unitInterval, StdSimplex ℝ (Fin (k + 1))) :=
  ⟨fun z ↦ StdSimplex.map g (BassH1Order.h1Parameter.{u} z), by fun_prop⟩
def plus : C(unitInterval × unitInterval, StdSimplex ℝ (Fin (k + 1))) :=
  ⟨fun z ↦ StdSimplex.map g (BassH1Order.plusParameter z), by fun_prop⟩
def minus : C(unitInterval × unitInterval, StdSimplex ℝ (Fin (k + 1))) :=
  ⟨fun z ↦ StdSimplex.map g (BassH1Order.minusParameter z), by fun_prop⟩
def bottom : C(unitInterval × unitInterval, StdSimplex ℝ (Fin (k + 1))) :=
  ⟨fun z ↦ StdSimplex.map g (BassH1Order.bottomParameter.{u} z), by fun_prop⟩
def vertex : C(unitInterval × unitInterval, StdSimplex ℝ (Fin (k + 1))) :=
  ⟨fun z ↦ StdSimplex.map f (BassMVertexOrder.parameter.{u} z), by fun_prop⟩
def second : C(unitInterval × unitInterval, StdSimplex ℝ (Fin (k + 1))) :=
  ⟨fun z ↦ StdSimplex.map g (BassMReassociation.secondParameter z), by fun_prop⟩

variable (e : IndexEqualities f g)

include e in
/-- The complete original M source agrees with the unchanged H0 target after exact relabeling. -/
theorem vertex_zero (t : unitInterval) : vertex.{u} f (0, t) = h0 g (1, t) := by
  rcases three_cover t with ⟨s, rfl⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩
  · change StdSimplex.map f _ = StdSimplex.map g _
    rw [← source_plus_parameter, ← old_source_plus_parameter]
    exact map_index_values f g _ _ e.sourcePlus _
  · change StdSimplex.map f _ = StdSimplex.map g _
    rw [← source_middle_parameter, ← old_source_middle_parameter]
    exact map_index_values f g _ _ e.sourceMiddle _
  · change StdSimplex.map f _ = StdSimplex.map g _
    rw [← source_minus_parameter, ← old_source_minus_parameter]
    exact map_index_values f g _ _ e.sourceMinus _

include e in
/-- The entire stage seam is the literal original five-piece word, with every dyadic speed kept. -/
theorem stage_join (t : unitInterval) : vertex.{u} f (1, t) = second g (0, t) := by
  change StdSimplex.map f _ = StdSimplex.map g _
  rw [BassMReassociation.second_zero]
  rcases three_cover t with ⟨s, rfl⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩
  · rw [path_lower]
    rcases cover s with ⟨q, rfl⟩ | ⟨q, rfl⟩
    · rw [path_lower, ← target_first_plus_parameter, ← old_first_plus_word]
      exact map_index_values f g _ _ e.firstPlus _
    · rw [path_upper, ← target_second_plus_parameter, ← old_second_plus_word]
      exact map_index_values f g _ _ e.secondPlus _
  · rw [path_upper, path_lower, ← target_middle_parameter, ← old_middle_word]
    exact map_index_values f g _ _ e.middle _
  · rw [path_upper, path_upper]
    rcases cover s with ⟨q, rfl⟩ | ⟨q, rfl⟩
    · rw [path_lower, ← target_second_minus_parameter, ← old_second_minus_word]
      exact map_index_values f g _ _ e.secondMinus _
    · rw [path_upper, ← target_first_minus_parameter, ← old_first_minus_word]
      exact map_index_values f g _ _ e.firstMinus _

/-- The two original stages are continuously pasted along their proved complete scalar seam. -/
def parameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin (k + 1))) :=
  concatFirst (vertex.{u} f) (second g) (stage_join f g e)

theorem parameter_lower (r t : unitInterval) :
    parameter.{u} f g e (lower r, t) = vertex.{u} f (r, t) :=
  concatFirst_lower _ _ _ r t

theorem parameter_upper (r t : unitInterval) :
    parameter.{u} f g e (upper r, t) = second g (r, t) :=
  concatFirst_upper _ _ _ r t

/-- The whole original M/H0 scalar edge follows from the three unchanged source words. -/
theorem parameter_zero (t : unitInterval) : parameter.{u} f g e (0, t) = h0 g (1, t) :=
  (concatFirst_zero _ _ _ t).trans (vertex_zero f g e t)

/-- The whole original M/H1 scalar edge retains the unchanged reassociation endpoint. -/
theorem parameter_one (t : unitInterval) : parameter.{u} f g e (1, t) = h1.{u} g (1, t) :=
  (concatFirst_one _ _ _ t).trans
    (congrArg (StdSimplex.map g) (BassMReassociation.second_one t))

/-- The complete positive scalar side retains both its original moving half and terminal pause. -/
theorem parameter_plus (r : unitInterval) : parameter.{u} f g e (r, 0) = plus g (r, 1) := by
  rcases cover r with ⟨s, rfl⟩ | ⟨s, rfl⟩
  · rw [parameter_lower]
    change StdSimplex.map f _ = StdSimplex.map g _
    rw [← vertex_plus_side_parameter, ← old_plus_side_lower]
    exact map_index_values f g _ _ e.sidePlus _
  · rw [parameter_upper]
    change StdSimplex.map g _ = StdSimplex.map g _
    rw [second_plus_side, old_plus_side_upper]

/-- The inverse scalar side keeps its own original reference endpoint and the same native pause. -/
theorem parameter_minus (r : unitInterval) : parameter.{u} f g e (r, 1) = minus g (r, 1) := by
  rcases cover r with ⟨s, rfl⟩ | ⟨s, rfl⟩
  · rw [parameter_lower]
    change StdSimplex.map f _ = StdSimplex.map g _
    rw [← vertex_minus_side_parameter, ← old_minus_side_lower]
    exact map_index_values f g _ _ e.sideMinus _
  · rw [parameter_upper]
    change StdSimplex.map g _ = StdSimplex.map g _
    rw [second_minus_side, old_minus_side_upper]

end Quillen.PerfectComplexes.BassMScalarPasting
