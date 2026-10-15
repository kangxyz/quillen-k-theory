/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassSupportOrder
public import Quillen.Topology.Realization.SimplexGridColumn

/-! Literal scalar shared edges after the checked support reindexing.
The scalar arrangement alone does not construct a coefficient ModelSimplex. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory Convexity Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassSupportOrder

/-- Affine relabeling preserves an original edge without needing a global order. -/
theorem map_any_edge {k l : ℕ} (f : Fin (k + 1) → Fin (l + 1))
    (i j : Fin (k + 1)) (t : unitInterval) :
    StdSimplex.map f (edge i j t) = edge (f i) (f j) t :=
  StdSimplex.map_duple (unitInterval.nonneg (unitInterval.symm t))
    (unitInterval.nonneg t) (by simp) i j f

/-- Both original half-speed normalization segments are retained by any affine relabeling. -/
theorem map_any_binary {k l : ℕ} (f : Fin (k + 1) → Fin (l + 1))
    (i j m : Fin (k + 1)) (t : unitInterval) :
    StdSimplex.map f (binaryPath i j m t) = binaryPath (f i) (f j) (f m) t :=
  map_trans_values _ _ _ _ _ (map_any_edge f i j) (map_any_edge f j m) t

/-- The exact reversed-and-concatenated five-node path is preserved with its native speeds. -/
theorem map_two_binary {k l : ℕ} (f : Fin (k + 1) → Fin (l + 1))
    (i j m n p : Fin (k + 1)) (t : unitInterval) :
    StdSimplex.map f (((binaryPath i j m).symm.trans (binaryPath i n p)) t) =
      ((binaryPath (f i) (f j) (f m)).symm.trans (binaryPath (f i) (f n) (f p))) t :=
  map_trans_values _ _ _ _ _ (fun s ↦ map_any_binary f i j m (unitInterval.symm s))
    (map_any_binary f i n p) t

theorem two_binary_congr {k : ℕ} {i j m n p i' j' m' n' p' : Fin (k + 1)}
    (hi : i = i') (hj : j = j') (hm : m = m') (hn : n = n') (hp : p = p')
    (t : unitInterval) :
    ((binaryPath i j m).symm.trans (binaryPath i n p)) t =
      ((binaryPath i' j' m').symm.trans (binaryPath i' n' p')) t := by
  subst i'
  subst j'
  subst m'
  subst n'
  subst p'
  rfl

/-- The positive chart parameter relabeled by `oldIndex` into the 63 scalar slots. -/
def plusParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 63)) :=
  ⟨fun z ↦ StdSimplex.map oldIndex (BassReferenceMerge.plusParameter z), by fun_prop⟩
/-- The inverse-coordinate chart parameter relabeled by `oldIndex` into the 63 scalar slots. -/
def minusParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 63)) :=
  ⟨fun z ↦ StdSimplex.map oldIndex (BassReferenceMerge.minusParameter z), by fun_prop⟩
/-- The bottom grid parameter relabeled by `oldIndex` into the 63 scalar slots. -/
def bottomParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 63)) :=
  ⟨fun z ↦ StdSimplex.map oldIndex (BassReferenceMerge.bottomParameter.{u} z), by fun_prop⟩
/-- The H0 parameter relabeled by `h0Index` into the 63 scalar slots. -/
def h0Parameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 63)) :=
  ⟨fun z ↦ StdSimplex.map h0Index (BassH0Diagram.parameter z), by fun_prop⟩

theorem paused_chart_zero (s : unitInterval) :
    DoubleSquareScalarPaths.coefficientPausedSquareParameter (0, s) =
      DoubleSquareScalarPaths.outerSquarePath s :=
  collapsed_zero_path _ s

/-- Entire positive H0/chart edge equality, including each original reversal and speed. -/
theorem h0_plus_scalar (s : unitInterval) : h0Parameter (s, 0) = plusParameter (0, s) := by
  change StdSimplex.map h0Index (BassH0Diagram.parameter (s, 0)) =
    StdSimplex.map oldIndex (StdSimplex.map BassReferenceMerge.chartFace.toOrderHom
      (StdSimplex.map BassOverlap.plusFace.toOrderHom
        (DoubleSquareScalarPaths.coefficientPausedSquareParameter (0, s))))
  rw [BassH0Diagram.parameter_left, paused_chart_zero,
    ← StdSimplex.map_comp, ← StdSimplex.map_comp]
  change StdSimplex.map h0Index
      (((binaryPath (k := 30) 9 10 11).symm.trans (binaryPath 9 12 13)) s) =
    StdSimplex.map _
      (((binaryPath (k := 17) 0 14 15).symm.trans (binaryPath 0 1 2)) s)
  rw [map_two_binary, map_two_binary]
  rfl

/-- Entire inverse H0/chart edge equality, retaining the distinct inverse chart. -/
theorem h0_minus_scalar (s : unitInterval) : h0Parameter (s, 1) = minusParameter (0, s) := by
  change StdSimplex.map h0Index (BassH0Diagram.parameter (s, 1)) =
    StdSimplex.map oldIndex (StdSimplex.map BassReferenceMerge.chartFace.toOrderHom
      (StdSimplex.map BassOverlap.minusFace.toOrderHom
        (DoubleSquareScalarPaths.coefficientPausedSquareParameter (0, s))))
  rw [BassH0Diagram.parameter_right, paused_chart_zero,
    ← StdSimplex.map_comp, ← StdSimplex.map_comp]
  change StdSimplex.map h0Index
      (((binaryPath (k := 30) 20 21 22).symm.trans (binaryPath 20 23 24)) s) =
    StdSimplex.map _
      (((binaryPath (k := 17) 0 14 15).symm.trans (binaryPath 0 1 2)) s)
  rw [map_two_binary, map_two_binary]
  simp only [Function.comp_apply]
  have h20 : h0Index 20 = oldIndex (BassReferenceMerge.chartFace.toOrderHom
      (BassOverlap.minusFace.toOrderHom 0)) := rfl
  have h21 : h0Index 21 = oldIndex (BassReferenceMerge.chartFace.toOrderHom
      (BassOverlap.minusFace.toOrderHom 14)) := rfl
  have h22 : h0Index 22 = oldIndex (BassReferenceMerge.chartFace.toOrderHom
      (BassOverlap.minusFace.toOrderHom 15)) := rfl
  have h23 : h0Index 23 = oldIndex (BassReferenceMerge.chartFace.toOrderHom
      (BassOverlap.minusFace.toOrderHom 1)) := rfl
  have h24 : h0Index 24 = oldIndex (BassReferenceMerge.chartFace.toOrderHom
      (BassOverlap.minusFace.toOrderHom 2)) := rfl
  exact two_binary_congr h20 h21 h22 h23 h24 s

/-- The source edge of the actual product parameter is its original five-node Bass path. -/
theorem bottom_zero (t : unitInterval) :
    BassLaurentBottomFace.parameter.{u} (0, t) =
      ((binaryPath (k := 14) 0 3 6).symm.trans (binaryPath 0 9 12)) t := by
  change Quillen.SimplexGrid.parameter.{u + 1} 4 2
    (BassProjectionPath.parameter t, binaryPath (k := 2) 0 1 2 0) = _
  rw [Path.source, Quillen.SimplexGrid.parameter_column]
  exact map_two_binary (Quillen.SimplexGrid.columnFace 4 2 0).toOrderHom 0 1 2 3 4 t

/-- Entire H0/bottom shared edge equality from the actual realized-product column restriction. -/
theorem h0_bottom_scalar (t : unitInterval) :
    h0Parameter (0, t) = bottomParameter.{u} (0, t) := by
  change StdSimplex.map h0Index (BassH0Diagram.parameter (0, t)) =
    StdSimplex.map oldIndex (StdSimplex.map BassReferenceMerge.bottomFace.toOrderHom
      (BassLaurentBottomFace.parameter (0, t)))
  rw [BassH0Diagram.parameter_zero, bottom_zero, ← StdSimplex.map_comp]
  change StdSimplex.map h0Index
      (((binaryPath (k := 30) 2 3 11).symm.trans (binaryPath 2 14 22)) t) =
    StdSimplex.map _
      (((binaryPath (k := 14) 0 3 6).symm.trans (binaryPath 0 9 12)) t)
  rw [map_two_binary, map_two_binary]
  rfl

end Quillen.PerfectComplexes.BassSupportOrder
