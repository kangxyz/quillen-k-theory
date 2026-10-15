/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.ProjectionPasteLift
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassH0Diagram

/-! Exact face embeddings of the original rectangle's scalar source and target words. -/
@[expose] public section


noncomputable section
set_option autoImplicit false
open CategoryTheory Convexity Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
namespace Quillen.PerfectComplexes.ProjectionRectangleParameters
variable {k : ℕ} (α : ⦋17⦌ ⟶ ⦋k⦌)

/-- The source-chart binary path through rectangle vertices `2, 3, 11`, relabeled by `α`. -/
abbrev D := binaryPath (α.toOrderHom 2) (α.toOrderHom 3) (α.toOrderHom 11)
/--
The reversed source-total path followed by the target-total path, with vertex word `2, 1, 0, 14,
15` relabeled by `α`.
-/
abbrev T := (binaryPath (α.toOrderHom 0) (α.toOrderHom 1) (α.toOrderHom 2)).symm.trans
  (binaryPath (α.toOrderHom 0) (α.toOrderHom 14) (α.toOrderHom 15))
/-- The target-chart binary path through rectangle vertices `15, 16, 17`, relabeled by `α`. -/
abbrev K := binaryPath (α.toOrderHom 15) (α.toOrderHom 16) (α.toOrderHom 17)
/-- The first square comparison with vertex word `11, 10, 9, 12, 13`, relabeled by `α`. -/
abbrev L := (binaryPath (α.toOrderHom 9) (α.toOrderHom 10) (α.toOrderHom 11)).symm.trans
  (binaryPath (α.toOrderHom 9) (α.toOrderHom 12) (α.toOrderHom 13))
/-- The second square comparison with vertex word `13, 6, 5, 7, 17`, relabeled by `α`. -/
abbrev Ppath := (binaryPath (α.toOrderHom 5) (α.toOrderHom 6) (α.toOrderHom 13)).symm.trans
  (binaryPath (α.toOrderHom 5) (α.toOrderHom 7) (α.toOrderHom 17))

private theorem map_binary_symm (i j m : Fin 18) (t : unitInterval) :
    embed α ((binaryPath i j m).symm t) =
      (binaryPath (α.toOrderHom i) (α.toOrderHom j) (α.toOrderHom m)).symm t :=
  map_binaryPath α i j m (unitInterval.symm t)

/-- Whole original source word, including both native square paths and their exact speeds. -/
theorem source_mapped (t : unitInterval) :
    embed α (((DoubleSquareScalarPaths.firstRestriction.symm.trans
      DoubleSquareScalarPaths.secondRestriction).trans
        (DoubleSquareScalarPaths.middleChart.symm.trans
          DoubleSquareScalarPaths.lastRestriction)) t) =
      ((L α).trans (Ppath α)) t :=
  map_trans_values (embed α) _ _ _ _
    (map_trans_values (embed α) _ _ _ _ (map_binary_symm α 9 10 11) (map_binaryPath α 9 12 13))
    (map_trans_values (embed α) _ _ _ _ (map_binary_symm α 5 6 13) (map_binaryPath α 5 7 17)) t

/-- Whole original outer route; its central path will be shared by the two chart embeddings. -/
theorem target_mapped (t : unitInterval) :
    embed α ((DoubleSquareScalarPaths.sourceChart.symm.trans
      ((DoubleSquareScalarPaths.sourceTotal.symm.trans DoubleSquareScalarPaths.targetTotal).trans
        DoubleSquareScalarPaths.targetChart)) t) =
      ((D α).symm.trans ((T α).trans (K α))) t :=
  map_trans_values (embed α) _ _ _ _ (map_binary_symm α 2 3 11)
    (map_trans_values (embed α) _ _ _ _
      (map_trans_values (embed α) _ _ _ _ (map_binary_symm α 0 1 2) (map_binaryPath α 0 14 15))
      (map_binaryPath α 15 16 17)) t

/-- The original entire rectangle surface, with only its complete scalar face embedded. -/
def rectangle : ((L α).trans (Ppath α)).Homotopy ((D α).symm.trans ((T α).trans (K α))) :=
  Path.Homotopy.mapOfPaths (embed α) DoubleSquareScalarPaths.rectangleParameter _ _
    (source_mapped α) (target_mapped α)

end Quillen.PerfectComplexes.ProjectionRectangleParameters
namespace Quillen.PerfectComplexes.BassH0Diagram
open ProjectionRectangleParameters

/-- Both projection rectangles use literally the same scalar outer path. -/
theorem common_outer_path : T plusFace = T minusFace := rfl

/-- The full original two-chart boundary, including the actual outer-track cancellation. -/
def boundaryParameter := Path.Homotopy.pasteProjectionSquares
  (rectangle plusFace) (rectangle minusFace)

/-- The original two-parameter cylinder face after the actual ThreeSideSquare collapse. -/
def parameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 31)) :=
  collapsed boundaryParameter

end Quillen.PerfectComplexes.BassH0Diagram
