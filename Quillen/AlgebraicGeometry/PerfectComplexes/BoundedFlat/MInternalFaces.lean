/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MInternalBoundaryRows

/-! Actual common diagrams and complete scalar edges on the two first-stage M seams. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.PolynomialBaseChange AlgebraicGeometry.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMJoin
open BassMComponents BassMReferences

/-- The literal coefficient-composition edge of the native polynomial moving square. -/
def movingSourceFace : ⦋2⦌ ⟶ ⦋17⦌ :=
  SimplexCategory.Hom.mk ⟨![2, 3, 11], by decide⟩

/-- All source-edge parameters retain the actual original native binary coefficient path. -/
theorem moving_source_parameter (r : unitInterval) :
    StdSimplex.map movingSourceFace.toOrderHom (binaryPath (k := 2) 0 1 2 r) =
      DoubleSquareScalarPaths.coefficientMovingSquareParameter (r, 1) :=
  (map_binaryPath movingSourceFace 0 1 2 r).trans
    (collapsed_right_path DoubleSquareScalarPaths.coefficientBoundaryParameter r).symm

/-- The middle positive endpoint is the entire original coefficient path on its fixed column. -/
theorem middle_plus_parameter (r : unitInterval) :
    StdSimplex.map (Quillen.SimplexGrid.columnFace 2 4 2).toOrderHom
      (binaryPath (k := 2) 0 1 2 r) = middleParameter.{u} (r, 0) := by
  change _ = Quillen.SimplexGrid.parameter 2 4
    (binaryPath (k := 2) 0 1 2 r, BassProjectionPath.parameter 0)
  rw [Path.source]
  exact (Quillen.SimplexGrid.parameter_column 2 4 2 (binaryPath (k := 2) 0 1 2 r)).symm

/-- The distinct inverse endpoint retains the complete coefficient path on its own column. -/
theorem middle_minus_parameter (r : unitInterval) :
    StdSimplex.map (Quillen.SimplexGrid.columnFace 2 4 4).toOrderHom
      (binaryPath (k := 2) 0 1 2 r) = middleParameter.{u} (r, 1) := by
  change _ = Quillen.SimplexGrid.parameter 2 4
    (binaryPath (k := 2) 0 1 2 r, BassProjectionPath.parameter 1)
  rw [Path.target]
  exact (Quillen.SimplexGrid.parameter_column 2 4 4 (binaryPath (k := 2) 0 1 2 r)).symm

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The whole positive internal triangle agrees with its product column as an actual diagram. -/
theorem plus_internal_face : (plusSimplex P u v).face movingSourceFace =
    (middleSimplex P u v).face (Quillen.SimplexGrid.columnFace 2 4 2) := by
  change ((polynomialSimplex P u v).postcomp
    (BassH0Merge.normalizedMap (coefficientMap P ((underToLaurent R).app c)))).face _ = _
  rw [← moving_original P u v (underToLaurent R) (laurentPlus_projection P c),
    ← middle_original, ModelSimplex.ofIsos_face, ModelSimplex.ofIsos_face]
  apply ModelSimplex.ofIsos_nodes_congr
  intro i
  fin_cases i
  · exact plus_internal_nodes P u v 0
  · exact plus_internal_nodes P u v 1
  · exact plus_internal_nodes P u v 2

/-- The inverse internal triangle retains its full references under the actual reversal. -/
theorem minus_internal_face : (minusSimplex P u v).face movingSourceFace =
    (middleSimplex P u v).face (Quillen.SimplexGrid.columnFace 2 4 4) := by
  change ((polynomialSimplex P u v).postcomp
    (BassH0Merge.normalizedMap (coefficientMap P ((underToLaurentInvert R).app c)))).face _ = _
  rw [← moving_original P u v (underToLaurentInvert R) (laurentMinus_projection P c),
    ← middle_original, ModelSimplex.ofIsos_face, ModelSimplex.ofIsos_face]
  apply ModelSimplex.ofIsos_nodes_congr
  intro i
  fin_cases i
  · exact minus_internal_nodes P u v 0
  · exact minus_internal_nodes P u v 1
  · exact minus_internal_nodes P u v 2

/-- The whole positive seam uses one actual binary diagram for every original level and input. -/
theorem plus_internal_value (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (plusSimplex P u v) n
      (DoubleSquareScalarPaths.coefficientMovingSquareParameter (r, 1), x) =
    prespectrumSimplexFamily (middleSimplex P u v) n (middleParameter.{u} (r, 0), x) := by
  rw [← moving_source_parameter, prespectrumSimplexFamily_face, plus_internal_face,
    ← prespectrumSimplexFamily_face, middle_plus_parameter]

/-- The whole inverse seam uses its genuine separate boundary triangle at every original level. -/
theorem minus_internal_value (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (minusSimplex P u v) n
      (DoubleSquareScalarPaths.coefficientMovingSquareParameter (r, 1), x) =
    prespectrumSimplexFamily (middleSimplex P u v) n (middleParameter.{u} (r, 1), x) := by
  rw [← moving_source_parameter, prespectrumSimplexFamily_face, minus_internal_face,
    ← prespectrumSimplexFamily_face, middle_minus_parameter]

end Quillen.PerfectComplexes.BassMJoin
