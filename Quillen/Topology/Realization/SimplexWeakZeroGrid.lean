/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Topology.Realization.SimplexGridColumn

/-!
# Collapsing the zero row of the actual product grid

The initial row collapses to the chosen zero vertex while the positive row preserves each
original index after a retained reference vertex. The continuous parameter is the image of
the actual realization-product parameter, not an asserted affine cone parameter.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Convexity
open scoped Simplicial Topology
universe u
namespace Quillen.SimplexGrid.WeakZeroCollapse

/-- Initial zero row collapses; the retained reference vertex is skipped by the second row. -/
def collapseValue (q : ℕ) (i : Fin (SimplexGrid.dimension 1 q + 1)) : Fin (q + 3) :=
  if h : i.val ≤ q then 0 else
    ⟨i.val - q + 1, by
      have hi := i.isLt
      simp only [SimplexGrid.dimension, one_mul] at hi
      omega⟩

/-- The collapse preserves the entire directed order; no weak edge is reversed. -/
def collapse (q : ℕ) : ⦋SimplexGrid.dimension 1 q⦌ ⟶ ⦋q + 2⦌ :=
  SimplexCategory.Hom.mk ⟨collapseValue q, by
    intro i j hij
    have h := hij
    change i.val ≤ j.val at h
    simp only [collapseValue]
    split_ifs <;> simp_all only [Fin.le_def, Fin.val_zero] <;> omega⟩

/-- Every actual initial-row vertex is the same literal chosen-zero vertex. -/
theorem collapse_zero (q : ℕ) (j : Fin (q + 1)) :
    (collapse q).toOrderHom (SimplexGrid.index 1 q (0, j)) = 0 := by
  apply Fin.ext
  have hj := j.isLt
  change (collapseValue q (SimplexGrid.index 1 q (0, j))).val = 0
  simp only [collapseValue, SimplexGrid.index]
  split_ifs <;> simp_all

/-- Every actual terminal-row vertex retains its full normalization index. -/
theorem collapse_one (q : ℕ) (j : Fin (q + 1)) :
    (collapse q).toOrderHom (SimplexGrid.index 1 q (1, j)) = j.succ.succ := by
  apply Fin.ext
  have hj := j.isLt
  change (collapseValue q (SimplexGrid.index 1 q (1, j))).val = j.val + 1 + 1
  simp only [collapseValue, SimplexGrid.index]
  split_ifs <;> simp_all <;> omega

variable {q : ℕ}

/-- Preserve the actual realization-product parameter, without an affine-cone assertion. -/
def parameter : C(StdSimplex ℝ (Fin 2) × StdSimplex ℝ (Fin (q + 1)),
    StdSimplex ℝ (Fin (q + 3))) :=
  ⟨fun z ↦ StdSimplex.map (collapse q).toOrderHom (SimplexGrid.parameter.{u} 1 q z),
    by fun_prop⟩

/-- The initial entire product face is the unchanged zero vertex. -/
theorem parameter_zero (w : StdSimplex ℝ (Fin (q + 1))) :
    parameter (StdSimplex.single 0, w) = StdSimplex.single 0 := by
  change StdSimplex.map (collapse q).toOrderHom
    (SimplexGrid.parameter 1 q (StdSimplex.single 0, w)) = _
  rw [SimplexGrid.parameter_row, ← StdSimplex.map_comp]
  have h : (collapse q).toOrderHom ∘ (SimplexGrid.rowFace 1 q 0).toOrderHom =
      fun _ ↦ (0 : Fin (q + 3)) := funext (collapse_zero q)
  rw [h]
  exact StdSimplex.map_const _ _

/-- The terminal entire product face retains the original normalization simplex. -/
theorem parameter_one (w : StdSimplex ℝ (Fin (q + 1))) :
    parameter (StdSimplex.single 1, w) = StdSimplex.map Fin.succ (StdSimplex.map Fin.succ w) := by
  change StdSimplex.map (collapse q).toOrderHom
    (SimplexGrid.parameter 1 q (StdSimplex.single 1, w)) = _
  rw [SimplexGrid.parameter_row, ← StdSimplex.map_comp, ← StdSimplex.map_comp]
  congr 1
  exact funext (collapse_one q)


end Quillen.SimplexGrid.WeakZeroCollapse
