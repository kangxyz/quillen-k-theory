/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.MixedWeakZeroGrid
public import Quillen.Waldhausen.SConstruction.Iterated.SimplexPathEmbedding

/-!
# The actual product and affine cone parameters

The genuine collapsed product parameter and the separately specified affine cone retain
four complete common boundary paths. Their explicitly specified interpolation compares the
two interiors, without identifying or replacing either one. Every null clock is unchanged.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Convexity
open Quillen.SimplexParameters Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.SimplexGrid.WeakZeroProductComparison
variable {q : ℕ}

/-- The actual original grid parameter, with its original reversed null coordinate. -/
def product : C(I × StdSimplex ℝ (Fin (q + 1)), StdSimplex ℝ (Fin (q + 3))) :=
  WeakZeroCollapse.parameter.{u}.comp
    ⟨fun z ↦ ((edge (k := 1) 0 1).symm z.1, z.2), by fun_prop⟩

/-- The separately specified affine cone skips only the retained reference vertex. -/
def affine : C(I × StdSimplex ℝ (Fin (q + 1)), StdSimplex ℝ (Fin (q + 3))) :=
  CommonReferenceWeakZero.coneParameter.comp
    ⟨fun z ↦ (z.1, StdSimplex.map Fin.succ z.2), by fun_prop⟩

/-- The whole old normalization family is the initial face of the original product. -/
theorem product_zero (w : StdSimplex ℝ (Fin (q + 1))) :
    product.{u} (0, w) = StdSimplex.map Fin.succ (StdSimplex.map Fin.succ w) := by
  change WeakZeroCollapse.parameter ((edge (k := 1) 0 1).symm 0, w) = _
  rw [Path.source]
  exact WeakZeroCollapse.parameter_one w

/-- The whole terminal product face is the original zero vertex. -/
theorem product_one (w : StdSimplex ℝ (Fin (q + 1))) :
    product.{u} (1, w) = StdSimplex.single 0 := by
  change WeakZeroCollapse.parameter ((edge (k := 1) 0 1).symm 1, w) = _
  rw [Path.target]
  exact WeakZeroCollapse.parameter_zero w

/-- The original affine face has the same whole normalization boundary. -/
theorem affine_zero (w : StdSimplex ℝ (Fin (q + 1))) :
    affine (0, w) = StdSimplex.map Fin.succ (StdSimplex.map Fin.succ w) :=
  CommonReferenceWeakZero.cone_zero _

/-- The terminal affine face is the unchanged zero vertex. -/
theorem affine_one (w : StdSimplex ℝ (Fin (q + 1))) :
    affine (1, w) = StdSimplex.single 0 := CommonReferenceWeakZero.cone_one _

/-- The entire vertex column retains the actual original weak-edge time. -/
theorem product_vertex (j : Fin (q + 1)) (r : I) :
    product.{u} (r, StdSimplex.single j) = (edge (k := q + 2) 0 j.succ.succ).symm r := by
  change StdSimplex.map (WeakZeroCollapse.collapse q).toOrderHom
    (SimplexGrid.parameter 1 q ((edge (k := 1) 0 1).symm r, StdSimplex.single j)) = _
  rw [SimplexGrid.parameter_column, ← StdSimplex.map_comp]
  change embed (SimplexGrid.columnFace 1 q j ≫ WeakZeroCollapse.collapse q)
    (edge (k := 1) 0 1 (unitInterval.symm r)) = _
  rw [map_edge]
  change edge ((WeakZeroCollapse.collapse q).toOrderHom (SimplexGrid.index 1 q (0, j)))
    ((WeakZeroCollapse.collapse q).toOrderHom (SimplexGrid.index 1 q (1, j)))
      (unitInterval.symm r) = _
  rw [WeakZeroCollapse.collapse_zero, WeakZeroCollapse.collapse_one]
  rfl

/-- The corresponding affine column has exactly that same old null clock. -/
theorem affine_vertex (j : Fin (q + 1)) (r : I) :
    affine (r, StdSimplex.single j) = (edge (k := q + 2) 0 j.succ.succ).symm r := by
  change CommonReferenceWeakZero.coneParameter
    (r, StdSimplex.map Fin.succ (StdSimplex.single j)) = _
  rw [StdSimplex.map_single]
  exact CommonReferenceWeakZero.cone_vertex j r

variable {i j : Fin (q + 1)}
  (P : Path (StdSimplex.single i : StdSimplex ℝ (Fin (q + 1))) (StdSimplex.single j))

/-- A new specified interpolation, relative to all four complete old boundary paths. -/
def comparison : C(I × (I × I), StdSimplex ℝ (Fin (q + 3))) :=
  Quillen.simplexParameterInterpolation
    (product.{u}.comp ⟨fun z ↦ (z.1, P z.2), by fun_prop⟩)
    (affine.comp ⟨fun z ↦ (z.1, P z.2), by fun_prop⟩)

/-- The whole first surface is precisely the original product interior. -/
theorem comparison_zero (r s : I) :
    comparison.{u} P (0, (r, s)) = product.{u} (r, P s) := by
  simp [comparison, Quillen.simplexParameterInterpolation]

/-- The whole second surface is precisely the separately specified affine interior. -/
theorem comparison_one (r s : I) :
    comparison.{u} P (1, (r, s)) = affine (r, P s) := by
  simp [comparison, Quillen.simplexParameterInterpolation]

/-- The unchanged normalization word survives every interpolation time. -/
theorem comparison_null_zero (a s : I) :
    comparison.{u} P (a, (0, s)) =
      StdSimplex.map Fin.succ (StdSimplex.map Fin.succ (P s)) := by
  simp [comparison, Quillen.simplexParameterInterpolation, product_zero, affine_zero]

/-- The chosen zero vertex is fixed for the entire opposite face. -/
theorem comparison_null_one (a s : I) :
    comparison.{u} P (a, (1, s)) = StdSimplex.single 0 := by
  simp [comparison, Quillen.simplexParameterInterpolation, product_one, affine_one]

/-- The whole first weak-null column retains its original reversed time. -/
theorem comparison_source (a r : I) :
    comparison.{u} P (a, (r, 0)) = (edge (k := q + 2) 0 i.succ.succ).symm r := by
  simp [comparison, Quillen.simplexParameterInterpolation, product_vertex, affine_vertex]

/-- The whole second weak-null column retains its original reversed time. -/
theorem comparison_target (a r : I) :
    comparison.{u} P (a, (r, 1)) = (edge (k := q + 2) 0 j.succ.succ).symm r := by
  simp [comparison, Quillen.simplexParameterInterpolation, product_vertex, affine_vertex]

end Quillen.SimplexGrid.WeakZeroProductComparison
