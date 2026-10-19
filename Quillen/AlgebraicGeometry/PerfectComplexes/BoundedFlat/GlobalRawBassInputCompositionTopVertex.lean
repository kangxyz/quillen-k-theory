/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputCompositionTopInternalNodes
public import Quillen.Topology.Path.ScalarRectangleConcatenation
public import Quillen.Topology.Realization.SimplexGridBoundary

/-!
# The entire original global composition vertex stage in its actual carrier

Full reference-node identities glue the original positive square, middle product and reversed
inverse square. The complete carrier face has the original half/quarter/quarter overlap clocks
and recovers the whole first half of M, including every native level and independent structure
time. The second, reassociation half of M is not constructed here.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Convexity
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.LoopPrespectrum
open Quillen.NativePathCells Quillen.ScalarRectangle
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.GlobalRawBass.InputCompositionTopVertex

/-- The exact original base-composition edge of the polynomial moving rectangle. -/
def movingEdge : ⦋2⦌ ⟶ ⦋17⦌ := SimplexCategory.Hom.mk ⟨![2, 3, 11], by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩

/-- Every scalar point of the moving edge has the original split-composition clock. -/
theorem moving_parameter (r : unitInterval) :
    StdSimplex.map movingEdge.toOrderHom (binaryPath (k := 2) 0 1 2 r) =
      DoubleSquareScalarPaths.coefficientMovingSquareParameter (r, 1) :=
  (map_binaryPath movingEdge 0 1 2 r).trans
    (collapsed_right_path DoubleSquareScalarPaths.coefficientBoundaryParameter r).symm

/-- The entire positive product column has the same base-composition clock. -/
theorem middle_plus_parameter (r : unitInterval) :
    StdSimplex.map (Quillen.SimplexGrid.columnFace 2 4 2).toOrderHom
      (binaryPath (k := 2) 0 1 2 r) = InputCompositionTopPieces.middleParameter.{u} (r, 0) := by
  change _ = Quillen.SimplexGrid.parameter 2 4
    (binaryPath (k := 2) 0 1 2 r, InputIdentityProjection.parameter 0)
  rw [Path.source]
  exact (Quillen.SimplexGrid.parameter_column 2 4 2 (binaryPath (k := 2) 0 1 2 r)).symm

/-- The distinct inverse product column retains that original clock at its actual endpoint. -/
theorem middle_minus_parameter (r : unitInterval) :
    StdSimplex.map (Quillen.SimplexGrid.columnFace 2 4 4).toOrderHom
      (binaryPath (k := 2) 0 1 2 r) = InputCompositionTopPieces.middleParameter.{u} (r, 1) := by
  change _ = Quillen.SimplexGrid.parameter 2 4
    (binaryPath (k := 2) 0 1 2 r, InputIdentityProjection.parameter 1)
  rw [Path.target]
  exact (Quillen.SimplexGrid.parameter_column 2 4 4 (binaryPath (k := 2) 0 1 2 r)).symm

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
open InputCompositionTopPieces

/-- The complete positive internal seam agrees in the full original carrier. -/
theorem plus_middle (r : unitInterval) :
    movingFace f g plus plus_projection (r, 1) = middleFace f g (r, 0) := by
  have h := CommonReferenceNerve.parameter_eq_of_face_nodes
    (InputCompositionCarrierCharts.source f g) (middleNodes f g)
    (movingNodes f g plus plus_projection)
    (Quillen.SimplexGrid.columnFace 2 4 2) movingEdge (fun i ↦ ?_)
    (binaryPath (k := 2) 0 1 2 r)
  · exact (congrArg
      (CommonReferenceNerve.parameter (InputCompositionCarrierCharts.source f g)
        (movingNodes f g plus plus_projection)) (moving_parameter r)).symm.trans
      (h.trans (congrArg
        (CommonReferenceNerve.parameter (InputCompositionCarrierCharts.source f g)
          (middleNodes f g)) (middle_plus_parameter.{u} r)))
  · fin_cases i
    · exact InputCompositionTopInternalNodes.plus_internal_nodes f g 0
    · exact InputCompositionTopInternalNodes.plus_internal_nodes f g 1
    · exact InputCompositionTopInternalNodes.plus_internal_nodes f g 2

/-- The inverse internal seam retains the distinct original projection source reference. -/
theorem minus_middle (r : unitInterval) :
    movingFace f g minus minus_projection (r, 1) = middleFace f g (r, 1) := by
  have h := CommonReferenceNerve.parameter_eq_of_face_nodes
    (InputCompositionCarrierCharts.source f g) (middleNodes f g)
    (movingNodes f g minus minus_projection)
    (Quillen.SimplexGrid.columnFace 2 4 4) movingEdge (fun i ↦ ?_)
    (binaryPath (k := 2) 0 1 2 r)
  · exact (congrArg
      (CommonReferenceNerve.parameter (InputCompositionCarrierCharts.source f g)
        (movingNodes f g minus minus_projection)) (moving_parameter r)).symm.trans
      (h.trans (congrArg
        (CommonReferenceNerve.parameter (InputCompositionCarrierCharts.source f g)
          (middleNodes f g)) (middle_minus_parameter.{u} r)))
  · fin_cases i
    · exact InputCompositionTopInternalNodes.minus_internal_nodes f g 0
    · exact InputCompositionTopInternalNodes.minus_internal_nodes f g 1
    · exact InputCompositionTopInternalNodes.minus_internal_nodes f g 2

/-- The last original piece reverses only its overlap-height coordinate. -/
def minusFace : C(unitInterval × unitInterval, InputCompositionCarrierCharts.Carrier f g) :=
  (movingFace f g minus minus_projection).comp
    ⟨fun z ↦ (z.1, unitInterval.symm z.2), by fun_prop⟩

/-- The actual middle-to-inverse join includes the original reversal. -/
theorem middle_minus (r : unitInterval) :
    middleFace f g (r, 1) = minusFace f g (r, 0) := by
  change _ = movingFace f g minus minus_projection (r, unitInterval.symm 0)
  rw [unitInterval.symm_zero]
  exact (minus_middle f g r).symm

/-- The original final two vertex pieces joined along their proved whole carrier seam. -/
def tailFace : C(unitInterval × unitInterval, InputCompositionCarrierCharts.Carrier f g) :=
  concatSecond (middleFace f g) (minusFace f g) (middle_minus f g)

/-- The original positive piece joins the full remaining tail at every composition time. -/
theorem plus_tail (r : unitInterval) :
    movingFace f g plus plus_projection (r, 1) = tailFace f g (r, 0) :=
  (plus_middle f g r).trans (concatSecond_zero _ _ _ r).symm

/-- The entire original vertex stage, with its original overlap-height allocation. -/
def face : C(unitInterval × unitInterval, InputCompositionCarrierCharts.Carrier f g) :=
  concatSecond (movingFace f g plus plus_projection) (tailFace f g) (plus_tail f g)

/-- The complete first half of the overlap height is the unchanged positive moving square. -/
theorem face_plus (r t : unitInterval) :
    face f g (r, lower t) = movingFace f g plus plus_projection (r, t) :=
  concatSecond_lower _ _ _ r t

/-- The complete middle quarter retains both independent original parameters. -/
theorem face_middle (r t : unitInterval) :
    face f g (r, upper (lower t)) = middleFace f g (r, t) :=
  (concatSecond_upper _ _ _ r (lower t)).trans (concatSecond_lower _ _ _ r t)

/-- The complete final quarter keeps the original inverse-square reversal. -/
theorem face_minus (r t : unitInterval) :
    face f g (r, upper (upper t)) =
      movingFace f g minus minus_projection (r, unitInterval.symm t) :=
  (concatSecond_upper _ _ _ r (upper t)).trans (concatSecond_upper _ _ _ r t)

/-- All original vertex-stage parameters recover the exact native first half of M. -/
theorem face_native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputCompositionCarrierCharts.source f g)
      (face f g) n ((r, t), x) =
      (InputCompositionCharts.spanTrack f g).level n
        (lower r, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (projection.app Z))
          (boundedFlatPerfectPrespectrumMap (projection.app Z)) n (t, x)) := by
  rcases three_cover t with ⟨s, rfl⟩ | ⟨s, rfl⟩ | ⟨s, rfl⟩
  · have h := CommonReferenceNerve.compactPrespectrumFamily_eq_simplex
      (InputCompositionCarrierCharts.source f g) (face f g)
      (movingNodes f g plus plus_projection) (r, lower s)
      (DoubleSquareScalarPaths.coefficientMovingSquareParameter (r, s))
      (face_plus f g r s) n x
    have h' := CommonReferenceNerve.compactPrespectrumFamily_eq_simplex
      (InputCompositionCarrierCharts.source f g) (movingFace f g plus plus_projection)
      (movingNodes f g plus plus_projection) (r, s)
      (DoubleSquareScalarPaths.coefficientMovingSquareParameter (r, s)) rfl n x
    exact h.trans (h'.symm.trans (plus_top_cell f g n r s x))
  · have h := CommonReferenceNerve.compactPrespectrumFamily_eq_simplex
      (InputCompositionCarrierCharts.source f g) (face f g) (middleNodes f g)
      (r, upper (lower s)) (middleParameter.{u} (r, s)) (face_middle f g r s) n x
    have h' := CommonReferenceNerve.compactPrespectrumFamily_eq_simplex
      (InputCompositionCarrierCharts.source f g) (middleFace f g) (middleNodes f g)
      (r, s) (middleParameter.{u} (r, s)) rfl n x
    exact h.trans (h'.symm.trans (middle_top_cell f g n r s x))
  · have h := CommonReferenceNerve.compactPrespectrumFamily_eq_simplex
      (InputCompositionCarrierCharts.source f g) (face f g)
      (movingNodes f g minus minus_projection) (r, upper (upper s))
      (DoubleSquareScalarPaths.coefficientMovingSquareParameter (r, unitInterval.symm s))
      (face_minus f g r s) n x
    have h' := CommonReferenceNerve.compactPrespectrumFamily_eq_simplex
      (InputCompositionCarrierCharts.source f g) (movingFace f g minus minus_projection)
      (movingNodes f g minus minus_projection) (r, unitInterval.symm s)
      (DoubleSquareScalarPaths.coefficientMovingSquareParameter (r, unitInterval.symm s)) rfl n x
    exact h.trans (h'.symm.trans (minus_top_cell f g n r s x))

/-- Both original vertex-stage times remain independent of prespectrum structure time. -/
theorem face_structure (n : ℕ) (r t z : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputCompositionCarrierCharts.source f g)
      (face f g) (n + 1)
        ((r, t), (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).structureMap n x z) =
      (originalPrespectrum (boundedFlatPerfectWaldhausen (laurent.obj X))).structureMap n
        (CommonReferenceNerve.compactPrespectrumFamily (InputCompositionCarrierCharts.source f g)
          (face f g) n ((r, t), x)) z :=
  CommonReferenceNerve.compactPrespectrumFamily_structure _ _ n (r, t) x z

end Quillen.PerfectComplexes.GlobalRawBass.InputCompositionTopVertex
