/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1BottomRows

/-! The entire original H1 source edge in the unchanged H0/chart/bottom62 family. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.PolynomialBaseChange AlgebraicGeometry.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.LoopPrespectrum
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassH1Join

/-- The old bottom's literal target column, retained as an actual face in the fixed old62 family. -/
def oldBottomEdgeFace : ⦋4⦌ ⟶ ⦋62⦌ :=
  Quillen.SimplexGrid.columnFace 4 2 2 ≫ BassSupportOrder.bottomFace

/-- The unchanged target of the original bottom product parameter is its actual final column. -/
theorem bottom_target_parameter (t : unitInterval) :
    BassLaurentBottomFace.parameter.{u} (1, t) =
      StdSimplex.map (Quillen.SimplexGrid.columnFace 4 2 2).toOrderHom
        (NativeSquareFiveSimplex.parameter t) := by
  change Quillen.SimplexGrid.parameter.{u + 1} 4 2
    (BassProjectionPath.parameter t, binaryPath (k := 2) 0 1 2 1) = _
  rw [Path.target]
  exact Quillen.SimplexGrid.parameter_column 4 2 2 _

/-- Literal whole-edge scalar identity in the already fixed actual old62 coordinates. -/
theorem old_bottom_edge_parameter (t : unitInterval) :
    StdSimplex.map oldBottomEdgeFace.toOrderHom (NativeSquareFiveSimplex.parameter t) =
      BassSupportOrder.bottomParameter.{u} (1, t) := by
  change StdSimplex.map oldBottomEdgeFace.toOrderHom (NativeSquareFiveSimplex.parameter t) =
    StdSimplex.map BassSupportOrder.oldIndex
      (StdSimplex.map BassReferenceMerge.bottomFace.toOrderHom
        (BassLaurentBottomFace.parameter.{u} (1, t)))
  rw [bottom_target_parameter, ← StdSimplex.map_comp, ← StdSimplex.map_comp]
  rfl

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The whole first-component source simplex is the unchanged bottom edge of the old62 family. -/
theorem first_old62_bottom_face :
    (BassH1Components.firstSimplex P u v).face middleSourceFace =
      (BassH0Merged.simplex P u v).face oldBottomEdgeFace := by
  rw [← BassH1References.first_original]
  unfold BassH0Merged.simplex
  rw [ModelSimplex.ofIsos_face, ModelSimplex.ofIsos_face]
  exact ModelSimplex.ofIsos_nodes_congr _ _ (first_old62_bottom_nodes P u v)

/-- Every original source-edge input of H1 is evaluated in the fixed old62 family, at all levels. -/
theorem old62_h1_source_native (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (BassH0Merged.simplex P u v) n
      (BassSupportOrder.bottomParameter.{u} (1, t), x) =
    (boundedFlatCoefficientBassCompositeComparison P u v).level n
      (0, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x)) := by
  rw [← old_bottom_edge_parameter, prespectrumSimplexFamily_face, ← first_old62_bottom_face,
    ← prespectrumSimplexFamily_face, middle_source_parameter]
  have hz : Quillen.NativePathCells.lower 0 = 0 := by
    apply Subtype.ext
    simp [Quillen.NativePathCells.lower]
  simpa only [hz] using BassH1NativeCells.first_native P u v n 0 t x

end Quillen.PerfectComplexes.BassH1Join
