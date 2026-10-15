/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1MiddleBoundaryRows
public import Quillen.Topology.Path.ScalarPathCells
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassH1NativeCells

/-! One whole original shared middle-path face of the first and middle H1 component families. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.PolynomialBaseChange AlgebraicGeometry.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.LoopPrespectrum
open Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassH1Join

def firstMiddleFace : ⦋4⦌ ⟶ ⦋30⦌ :=
  SimplexCategory.Hom.mk ⟨![26, 27, 28, 29, 30], by decide⟩
def middleSourceFace : ⦋4⦌ ⟶ ⦋30⦌ :=
  SimplexCategory.Hom.mk ⟨![2, 3, 11, 14, 22], by decide⟩

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- All five dependent nodes, including both distinct raw intermediates, are genuinely shared. -/
theorem middle_path_nodes (i : Fin 5) :
    BassH1References.firstNodes P u v (firstMiddleFace.toOrderHom i) =
      BassH1References.middleNodes P u v (middleSourceFace.toOrderHom i) := by
  fin_cases i
  · exact first_middle_center P u v
  · exact plus_middle_nodes P u v 1
  · exact plus_middle_nodes P u v 2
  · exact minus_middle_nodes P u v 1
  · exact minus_middle_nodes P u v 2

/-- The entire original four-simplex diagram agrees, with every actual reference arrow. -/
theorem middle_face : (BassH1Components.firstSimplex P u v).face firstMiddleFace =
    (BassH1Components.middleSimplex P u v).face middleSourceFace := by
  rw [← BassH1References.first_original, ← BassH1References.middle_original]
  rw [ModelSimplex.ofIsos_face, ModelSimplex.ofIsos_face]
  exact ModelSimplex.ofIsos_nodes_congr _ _ (middle_path_nodes P u v)

/-- The exact target-middle path of H0(u), at the original second-quarter coordinate. -/
theorem first_middle_parameter (t : unitInterval) :
    StdSimplex.map firstMiddleFace.toOrderHom (NativeSquareFiveSimplex.parameter t) =
      BassH0Diagram.parameter (1, upper (lower t)) := by
  rw [BassH0Diagram.parameter_one, path_upper, path_lower]
  exact BassSupportOrder.map_two_binary firstMiddleFace.toOrderHom 0 1 2 3 4 t

/-- The entire source path of H0(v), with the same binary segments and speeds. -/
theorem middle_source_parameter (t : unitInterval) :
    StdSimplex.map middleSourceFace.toOrderHom (NativeSquareFiveSimplex.parameter t) =
      BassH0Diagram.parameter (0, t) := by
  rw [BassH0Diagram.parameter_zero]
  exact BassSupportOrder.map_two_binary middleSourceFace.toOrderHom 0 1 2 3 4 t

/-- A genuine common boundary diagram, constructed from the unchanged original component. -/
def middleBoundarySimplex := (BassH1Components.firstSimplex P u v).face firstMiddleFace

/-- Every original point of the shared H1 middle boundary is evaluated by that exact diagram. -/
theorem middle_boundary_native (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (middleBoundarySimplex P u v) n
      (NativeSquareFiveSimplex.parameter t, x) =
    (boundedFlatCoefficientBassCompositeComparison P u v).level n
      (lower 1, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (upper (lower t), x)) := by
  change prespectrumSimplexFamily ((BassH1Components.firstSimplex P u v).face firstMiddleFace) n
    (NativeSquareFiveSimplex.parameter t, x) = _
  rw [← prespectrumSimplexFamily_face, first_middle_parameter]
  exact BassH1NativeCells.first_native P u v n 1 (upper (lower t)) x

/-- The same entire diagram retains the actual original middle-cell source values. -/
theorem middle_boundary_native_other (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (middleBoundarySimplex P u v) n
      (NativeSquareFiveSimplex.parameter t, x) =
    (boundedFlatCoefficientBassCompositeComparison P u v).level n
      (upper 0, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (upper (lower t), x)) := by
  change prespectrumSimplexFamily ((BassH1Components.firstSimplex P u v).face firstMiddleFace) n
    (NativeSquareFiveSimplex.parameter t, x) = _
  rw [middle_face, ← prespectrumSimplexFamily_face, middle_source_parameter]
  exact BassH1NativeCells.middle_native P u v n 0 t x

end Quillen.PerfectComplexes.BassH1Join
