/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftPolynomialParameters
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1InternalNodeJoins
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1MiddleBoundaryRows
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ProjectionRectangleSquareRows
public import Quillen.Topology.Realization.SimplexGridColumn

/-!
# Finite common-reference parameters on both left-route sheets

`false` selects the ordinary sheet and `true` the actual commonUnit reanchoring.
The 25-node parameter has polynomial p time first and positive-chart q time second.
All attachment and time seams below are equalities before native evaluation.
The midpoint unit edge and both external seed seams are separate obligations.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveLeftCellParameters
open BassH0Merge BassH1Join CommonReferenceNerve
open CoefficientBassPositiveC1BoundaryLift CoefficientBassPositiveC0CarrierAttachment
open CoefficientBassPositiveLeftPolynomialParameters
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The shifted sheet retains its full commonUnit reference, not merely its native value. -/
def sheetNode (e : Bool) : Node (laurentReference P p q) → Node (laurentReference P p q) :=
  if e then anchorNode (LaurentUnitReferenceSpecialization.commonUnit P p q) else id

/-- The ordinary attachment for `false` and the `commonUnit` attachment for `true`. -/
def attach (e : Bool) : Node (polynomialReference P p q) → Node (laurentReference P p q) :=
  if e then shiftedAttachNode P p q else ordinaryAttachNode P p q

/-- The 25 product-chart nodes in the ordinary (`false`) or common-unit shifted (`true`) sheet. -/
abbrev productNodes (e : Bool) := fun i ↦ sheetNode P p q e
  (BassH1References.chartNodes P p q (underToLaurent R) (laurentPlus_projection P b) i)
/-- The first rectangle nodes in the ordinary (`false`) or common-unit shifted (`true`) sheet. -/
abbrev firstRectangleNodes (e : Bool) := fun i ↦ sheetNode P p q e
  (BassH1References.firstNodes P p q i)
/-- The middle rectangle nodes in the ordinary (`false`) or common-unit shifted (`true`) sheet. -/
abbrev middleRectangleNodes (e : Bool) := fun i ↦ sheetNode P p q e
  (BassH1References.middleNodes P p q i)

/-- The actual product characteristic map; only these finite nodes are used. -/
def Z (e : Bool) : C(I × I, |nerve (Codiscrete (Node (laurentReference P p q)))|) :=
  ⟨fun z ↦ parameter (laurentReference P p q) (productNodes P p q e)
    (Quillen.SimplexGrid.parameter.{u + 1} 4 4
      (NativeSquareFiveSimplex.parameter z.1, NativeSquareFiveSimplex.parameter z.2)),
    by fun_prop⟩

/-- The first rectangle polynomial boundary path in the sheet selected by `e`. -/
def firstMovement (e : Bool) : C(I, |nerve (Codiscrete (Node (laurentReference P p q)))|) :=
  (parameter (laurentReference P p q) (firstRectangleNodes P p q e)).comp
    (ProjectionRectangleParameters.Ppath BassH0Diagram.plusFace).toContinuousMap

/-- The middle rectangle polynomial boundary path in the sheet selected by `e`. -/
def secondMovement (e : Bool) : C(I, |nerve (Codiscrete (Node (laurentReference P p q)))|) :=
  (parameter (laurentReference P p q) (middleRectangleNodes P p q e)).comp
    (ProjectionRectangleParameters.Ppath BassH0Diagram.plusFace).toContinuousMap

/-- The middle rectangle positive-chart boundary path in the sheet selected by `e`. -/
def middleChart (e : Bool) : C(I, |nerve (Codiscrete (Node (laurentReference P p q)))|) :=
  (parameter (laurentReference P p q) (middleRectangleNodes P p q e)).comp
    (ProjectionRectangleParameters.L BassH0Diagram.plusFace).toContinuousMap

private theorem polynomial_row_parameter
    (N : Fin 31 → Node (laurentReference P p q)) (t : I) :
    parameter (laurentReference P p q) N
      (ProjectionRectangleParameters.Ppath BassH0Diagram.plusFace t) =
    parameter (laurentReference P p q)
      (fun i ↦ N (BassH0Diagram.plusFace.toOrderHom (polynomialWordIndex i)))
      (NativeSquareFiveSimplex.parameter t) := by
  rw [← ProjectionRectangleSquareRows.polynomial_parameter]
  obtain ⟨i, z, hz⟩ := BassH1Support.square_path_in t
  rw [← hz]
  exact parameter_supported _ _ _
    (BassH0Diagram.plusFace.toOrderHom ∘ ProjectionRectangleSquareRows.polynomialRow)
    (fun _ ↦ rfl) (BassH1Support.edgeFace i)
    (BassH0Diagram.plusFace.toOrderHom.monotone.comp
      (ProjectionRectangleSquareRows.primitive_rows_monotone 1 i)) z

private theorem chart_row_parameter
    (N : Fin 31 → Node (laurentReference P p q)) (t : I) :
    parameter (laurentReference P p q) N
      (ProjectionRectangleParameters.L BassH0Diagram.plusFace t) =
    parameter (laurentReference P p q)
      (fun i ↦ N (BassH0Diagram.plusFace.toOrderHom (chartWordIndex i)))
      (NativeSquareFiveSimplex.parameter t) := by
  rw [← ProjectionRectangleSquareRows.chart_parameter]
  obtain ⟨i, z, hz⟩ := BassH1Support.square_path_in t
  rw [← hz]
  exact parameter_supported _ _ _
    (BassH0Diagram.plusFace.toOrderHom ∘ ProjectionRectangleSquareRows.chartRow)
    (fun _ ↦ rfl) (BassH1Support.edgeFace i)
    (BassH0Diagram.plusFace.toOrderHom.monotone.comp
      (ProjectionRectangleSquareRows.primitive_rows_monotone 0 i)) z

/-- S1: the entire first rectangle polynomial movement is the lower product column. -/
theorem first_movement_Z (e : Bool) (t : I) :
    firstMovement P p q e t = Z P p q e (t, 0) := by
  change parameter (laurentReference P p q) (firstRectangleNodes P p q e)
      (ProjectionRectangleParameters.Ppath BassH0Diagram.plusFace t) =
    parameter (laurentReference P p q) (productNodes P p q e)
      (Quillen.SimplexGrid.parameter 4 4
        (NativeSquareFiveSimplex.parameter t, NativeSquareFiveSimplex.parameter 0))
  rw [polynomial_row_parameter P p q (firstRectangleNodes P p q e) t, Path.source,
    Quillen.SimplexGrid.parameter_column]
  exact (congrArg (fun N : Fin 5 → Node (laurentReference P p q) ↦
    parameter (laurentReference P p q) N (NativeSquareFiveSimplex.parameter t))
    (funext fun i ↦ congrArg (sheetNode P p q e) (plus_column_nodes P p q i))).trans
      (parameter_face (laurentReference P p q) (productNodes P p q e)
        (Quillen.SimplexGrid.columnFace 4 4 2) (NativeSquareFiveSimplex.parameter t)).symm

/-- S2: the whole upper product column is the attachment of the actual P family. -/
theorem Z_attach_first (e : Bool) (t : I) :
    Z P p q e (t, 1) = mapParameter (attach P p q e) (firstParameter P p q t) := by
  change parameter _ _
    (Quillen.SimplexGrid.parameter 4 4 (_, NativeSquareFiveSimplex.parameter 1)) = _
  rw [Path.target, Quillen.SimplexGrid.parameter_column, parameter_face]
  cases e
  · exact (first_attach_parameter P p q t).symm
  · exact (first_shifted_attach_parameter P p q t).symm

/-- S3: the complete second rectangle movement is the attachment of the actual Q family. -/
theorem second_movement_attach (e : Bool) (t : I) :
    secondMovement P p q e t =
      mapParameter (attach P p q e) (secondParameter P p q t) := by
  change parameter (laurentReference P p q) (middleRectangleNodes P p q e)
    (ProjectionRectangleParameters.Ppath BassH0Diagram.plusFace t) = _
  rw [polynomial_row_parameter P p q (middleRectangleNodes P p q e) t]
  cases e
  · exact (second_attach_parameter P p q t).symm
  · exact (second_shifted_attach_parameter P p q t).symm

/-- S4 chart component: the whole product right edge is the middle positive chart movement. -/
theorem Z_target_middle_chart (e : Bool) (t : I) :
    Z P p q e (1, t) = middleChart P p q e t := by
  change parameter _ _
    (Quillen.SimplexGrid.parameter 4 4 (NativeSquareFiveSimplex.parameter 1, _)) =
      parameter _ _ _
  rw [Path.target, Quillen.SimplexGrid.parameter_row, parameter_face]
  change parameter (laurentReference P p q)
      (fun i ↦ productNodes P p q e (Quillen.SimplexGrid.index 4 4 (4, i)))
      (NativeSquareFiveSimplex.parameter t) =
    parameter (laurentReference P p q) (middleRectangleNodes P p q e)
      (ProjectionRectangleParameters.L BassH0Diagram.plusFace t)
  rw [chart_row_parameter P p q (middleRectangleNodes P p q e) t]
  exact congrArg (fun N : Fin 5 → Node (laurentReference P p q) ↦
    parameter (laurentReference P p q) N (NativeSquareFiveSimplex.parameter t))
    (funext fun i ↦ congrArg (sheetNode P p q e) (plus_row_nodes P p q i).symm)

/-- S4 polynomial component: retain the complete reference-bearing M13 endpoint. -/
theorem polynomial_time_seam : firstParameter P p q 1 = secondParameter P p q 0 :=
  first_target_second_source_parameter P p q

private def firstPositiveFace : ⦋2⦌ ⟶ ⦋30⦌ :=
  SimplexCategory.Hom.mk
    ⟨fun i ↦ BassH0Diagram.plusFace.toOrderHom
      (DoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i)), by decide⟩
private def middlePositiveFace : ⦋2⦌ ⟶ ⦋30⦌ :=
  SimplexCategory.Hom.mk
    ⟨fun i ↦ BassH0Diagram.plusFace.toOrderHom (rectangleLeftIndex i), by decide⟩

/-- S4 positive component: equality of the entire original binary path, on either sheet. -/
theorem positive_time_seam (e : Bool) (s : I) :
    parameter (laurentReference P p q) (firstRectangleNodes P p q e)
      (ProjectionRectangleParameters.K BassH0Diagram.plusFace s) =
    parameter (laurentReference P p q) (middleRectangleNodes P p q e)
      (ProjectionRectangleParameters.D BassH0Diagram.plusFace s) := by
  have h₁ := map_binaryPath firstPositiveFace 0 1 2 s
  have h₂ := map_binaryPath middlePositiveFace 0 1 2 s
  change StdSimplex.map firstPositiveFace.toOrderHom
    ((binaryPath (0 : Fin 3) 1 2) s) =
      ProjectionRectangleParameters.K BassH0Diagram.plusFace s at h₁
  change StdSimplex.map middlePositiveFace.toOrderHom
    ((binaryPath (0 : Fin 3) 1 2) s) =
      ProjectionRectangleParameters.D BassH0Diagram.plusFace s at h₂
  rw [← h₁, ← h₂, parameter_face, parameter_face]
  exact congrArg (fun N : Fin 3 → Node (laurentReference P p q) ↦
    parameter (laurentReference P p q) N ((binaryPath (0 : Fin 3) 1 2) s))
    (funext fun i ↦ congrArg (sheetNode P p q e) (plus_middle_nodes P p q i))

end Quillen.PerfectComplexes.CoefficientBassPositiveLeftCellParameters
