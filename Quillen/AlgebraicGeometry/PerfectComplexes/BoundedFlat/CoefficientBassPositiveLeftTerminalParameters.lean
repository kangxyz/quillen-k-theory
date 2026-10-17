/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftCellParameters
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1SourceProductStrips
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1BottomRows
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1OuterNodeJoins

/-! The four full-reference terminal null pieces.

The first-route old endpoint uses its D and L rows, then the product row at polynomial
time zero, then P(0). The first/middle time-one seam is not used here. Both Laurent
sheets retain the actual commonUnit. Only the four ordered primitive edges of each
five-node word are used; its enclosing relabeling need not be monotone.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveLeftTerminalParameters
open BassH0Merge BassH1Join CommonReferenceNerve
open CoefficientBassPositiveC1BoundaryLift CoefficientBassPositiveLeftCellParameters
open CoefficientBassPositiveLeftPolynomialParameters CoefficientBassPositiveC0PolynomialEndpoints
open CoefficientBassPositiveC1SourceProductStrips
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- D is the original first H1 positive source row. -/
def oldPositiveParameter (e : Bool) : C(I, |nerve (Codiscrete (Node (laurentReference P p q)))|) :=
  (parameter (laurentReference P p q) (firstRectangleNodes P p q e)).comp
    (ProjectionRectangleParameters.D BassH0Diagram.plusFace).toContinuousMap

/-- H is the original first H1 chart row, with its reversed-first square clock. -/
def oldChartParameter (e : Bool) : C(I, |nerve (Codiscrete (Node (laurentReference P p q)))|) :=
  (parameter (laurentReference P p q) (firstRectangleNodes P p q e)).comp
    (ProjectionRectangleParameters.L BassH0Diagram.plusFace).toContinuousMap

/-- The terminal paused chart with the full reference of the selected sheet. -/
def terminalChartParameter (e : Bool) :
    C(I, |nerve (Codiscrete (Node (laurentReference P p q)))|) :=
  ⟨fun s ↦ parameter (laurentReference P p q)
    (fun i ↦ sheetNode P p q e (chartNodes P p q i))
    (DoubleSquareScalarPaths.coefficientPausedSquareParameter (1, s)), by fun_prop⟩

/-- All three D nodes equal the actual terminal positive-product column nodes. -/
theorem positive_nodes (i : Fin 3) :
    BassH1References.firstNodes P p q
      (BassH0Diagram.plusFace.toOrderHom (rectangleLeftIndex i)) =
    positiveNineNodes P p q (Quillen.SimplexGrid.index 2 2 (i, 2)) := by
  have hi : BassProjectionPath.plusFace.toOrderHom i = Fin.castAdd 2 i := by
    fin_cases i <;> rfl
  exact (first_bottom_plus_nodes P p q i).trans
    ((congrArg (fun j ↦ BassBottomCommonFamily.bottomNodes P p q
      (Quillen.SimplexGrid.index 4 2 (j, 2))) hi).trans
      (positiveNine_bottom_nodes P p q i 2).symm)

/-- All five H nodes equal the first original terminal chart word, including references. -/
theorem first_chart_nodes (i : Fin 5) :
    BassH1References.firstNodes P p q
      (BassH0Diagram.plusFace.toOrderHom (chartWordIndex i)) =
    chartNodes P p q (outerFirstWordIndex i) :=
  (congrArg (postReferenceNode (laurentReference P p q)
    (BassH1Components.laurentMap P q) (BassH1References.firstIso P p q))
    (BassH0Diagram.plus_nodes P p (chartWordIndex i))).trans
      (first_old_chart_word_nodes P p q (underToLaurent R)
        (laurentPlus_projection P a) (laurentPlus_projection P c) i)

/-- All five K nodes are the actual product row2 and the second original chart word. -/
theorem second_chart_nodes (i : Fin 5) :
    BassH1References.chartNodes P p q (underToLaurent R) (laurentPlus_projection P b)
      (Quillen.SimplexGrid.index 4 4 (2, i)) =
    chartNodes P p q (outerProductWordIndex i) :=
  product_old_chart_word_nodes P p q (underToLaurent R) (laurentPlus_projection P a)
    (laurentPlus_projection P b) (laurentPlus_projection P c) i

private def positiveFace : ⦋2⦌ ⟶ ⦋30⦌ :=
  SimplexCategory.Hom.mk
    ⟨fun i ↦ BassH0Diagram.plusFace.toOrderHom (rectangleLeftIndex i), by decide⟩

/-- The complete D parameter is the C1 positive target column at unchanged time. -/
theorem positive_parameter (e : Bool) (s : I) :
    oldPositiveParameter P p q e s =
      mapParameter (sheetNode P p q e) (positiveParameter P p q (1, s)) := by
  change parameter _ _ (ProjectionRectangleParameters.D BassH0Diagram.plusFace s) = _
  rw [positive_target, mapParameter_parameter]
  have h := map_binaryPath positiveFace 0 1 2 s
  change StdSimplex.map positiveFace.toOrderHom ((binaryPath (0 : Fin 3) 1 2) s) =
    ProjectionRectangleParameters.D BassH0Diagram.plusFace s at h
  rw [← h, parameter_face]
  exact congrArg (fun N : Fin 3 → Node (laurentReference P p q) ↦
    parameter (laurentReference P p q) N ((binaryPath (0 : Fin 3) 1 2) s))
    (funext fun i ↦ congrArg (sheetNode P p q e) (positive_nodes P p q i))

/-- Ordinary D keeps exactly the accepted positive target parameter. -/
theorem positive_ordinary (s : I) : oldPositiveParameter P p q false s =
    positiveParameter P p q (1, s) := by
  rw [positive_parameter]
  change mapParameter _ (parameter _ _ _) = parameter _ _ _
  rw [mapParameter_parameter]; rfl

/-- Shifted D keeps the actual commonUnit action on that entire target parameter. -/
theorem positive_shifted (s : I) : oldPositiveParameter P p q true s =
    shiftedPositiveParameter P p q (1, s) :=
  positive_parameter P p q true s

private theorem word_parameter {k : ℕ} (N : Fin (k + 1) → Node (laurentReference P p q))
    (f : Fin 5 → Fin (k + 1))
    (h : ∀ i : Fin 4, Monotone (f ∘ (BassH1Support.edgeFace i).toOrderHom)) (s : I) :
    parameter (laurentReference P p q) N (StdSimplex.map f (NativeSquareFiveSimplex.parameter s)) =
      parameter (laurentReference P p q) (fun i ↦ N (f i))
        (NativeSquareFiveSimplex.parameter s) := by
  obtain ⟨i, z, hz⟩ := BassH1Support.square_path_in s
  rw [← hz]
  exact parameter_supported _ _ _ f (fun _ ↦ rfl) (BassH1Support.edgeFace i) (h i) z

/-- H is exactly the first literal half of the terminal chart, on either sheet. -/
theorem first_chart_parameter (e : Bool) (s : I) :
    oldChartParameter P p q e s = terminalChartParameter P p q e (lower s) := by
  change parameter _ _ (ProjectionRectangleParameters.L BassH0Diagram.plusFace s) =
    parameter _ _ (DoubleSquareScalarPaths.coefficientPausedSquareParameter (1, lower s))
  rw [← ProjectionRectangleSquareRows.chart_parameter, ← old_chart_first_parameter]
  rw [word_parameter P p q _ _ (fun i ↦ BassH0Diagram.plusFace.toOrderHom.monotone.comp
      (ProjectionRectangleSquareRows.primitive_rows_monotone 0 i)),
    word_parameter P p q _ outerFirstWordIndex (by decide)]
  exact congrArg (fun N : Fin 5 → Node (laurentReference P p q) ↦
    parameter (laurentReference P p q) N (NativeSquareFiveSimplex.parameter s))
    (funext fun i ↦ congrArg (sheetNode P p q e) (first_chart_nodes P p q i))

/-- K is exactly the second literal half, with polynomial p fixed at time zero. -/
theorem second_chart_parameter (e : Bool) (s : I) :
    Z P p q e (0, s) = terminalChartParameter P p q e (upper s) := by
  change parameter _ _ (Quillen.SimplexGrid.parameter 4 4
    (NativeSquareFiveSimplex.parameter 0, NativeSquareFiveSimplex.parameter s)) =
    parameter _ _ (DoubleSquareScalarPaths.coefficientPausedSquareParameter (1, upper s))
  rw [Path.source, Quillen.SimplexGrid.parameter_row, parameter_face,
    ← old_chart_second_parameter,
    word_parameter P p q _ outerProductWordIndex (by decide)]
  exact congrArg (fun N : Fin 5 → Node (laurentReference P p q) ↦
    parameter (laurentReference P p q) N (NativeSquareFiveSimplex.parameter s))
    (funext fun i ↦ congrArg (sheetNode P p q e) (second_chart_nodes P p q i))

private theorem parameter_vertex {k : ℕ} (N : Fin (k + 1) → Node (polynomialReference P p q))
    (i : Fin (k + 1)) : parameter (polynomialReference P p q) N (StdSimplex.single i) =
      nodePoint (polynomialReference P p q) (N i) := by
  let α : ⦋0⦌ ⟶ ⦋k⦌ := SimplexCategory.Hom.mk ⟨fun _ ↦ i, fun _ _ _ ↦ le_refl i⟩
  have hm : StdSimplex.map α.toOrderHom
      (StdSimplex.single (0 : Fin 1) : StdSimplex ℝ (Fin 1)) = StdSimplex.single i := by
    rw [StdSimplex.map_single]; rfl
  rw [← hm, parameter_face]; rfl

/-- C17 uses the same full polynomial nerve point as the terminal paused C1 cylinder. -/
theorem polynomial_endpoint : firstParameter P p q 0 = polynomialParameter P p q 1 := by
  rw [first_source_parameter]
  change nodePoint _ _ = parameter _ _ (pausedBinaryParameter 1)
  rw [Path.target, parameter_vertex]

end Quillen.PerfectComplexes.CoefficientBassPositiveLeftTerminalParameters
