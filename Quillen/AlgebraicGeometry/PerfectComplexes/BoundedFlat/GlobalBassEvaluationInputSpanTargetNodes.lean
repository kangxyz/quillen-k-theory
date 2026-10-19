/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputCommutingRawNodes
public import
Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputSpanParameterNodes
public import
Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputRawChartProductNodes
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ReferenceWhiskeringFamily

/-!
# The original polynomial row in the attached span comparison

One complete terminal node pins the entire five-node raw polynomial square. Both representations
retain the same actual evaluation and raw chart suffix, with their original reference anchors.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.GlobalBassEvaluation.InputSpanTargetNodes
open GlobalSectionChangeIndex BassH0Merge BassH1Join
variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (k : laurent ⟶ polynomial)
  (hk : ∀ Z, k.app Z ≫ projection.app Z = GlobalRawBass.laurentProjection.app Z)

private abbrev rawSource := NativeSquareFiveSimplex.source (polynomial.map g) (projection.app Y)
private abbrev rawNodes := NativeSquareFiveSimplex.nodes (polynomial.map g) (projection.app Y)
  (projection.app X) g (projection.naturality g)

private def attachedAnchor : (InputMixedDesc.sourceMap g).functor ≅
    (evaluationModel (op Y) ≫ rawSource g ≫ evaluationRawMap (k.app X)).functor :=
  InputSpanParameterNodes.sourceIso g k hk ≪≫
    isoWhiskerRight (evaluationComparisonIso (polynomial.map g ≫ projection.app Y))
      (evaluationRawMap (k.app X)).functor

private def rectangleAnchor : (InputMixedDesc.sourceMap g).functor ≅
    (evaluationModel (op Y) ≫ rawSource g ≫ evaluationRawMap (k.app X)).functor :=
  evaluationComparisonIso (laurent.map g ≫ GlobalRawBass.laurentProjection.app Y) ≪≫
    isoWhiskerLeft (evaluationModel (op Y)).functor
      (ProjectionRectangleSquareRows.polynomialAnchor (projection.app Y) (k.app Y)
        (k.app X) (polynomial.map g) (laurent.map g) (k.naturality g)
        (GlobalRawBass.laurentProjection.app Y) (hk Y))

private theorem attached_nodes (i : Fin 5) :
    InputSpanParameterNodes.nodes g k hk (InputCommutingRawNodes.rawIndex i) =
      prePostNodes (InputMixedDesc.sourceMap g) (evaluationModel (op Y))
        (evaluationRawMap (k.app X)) (rawSource g) (rawNodes g)
        (attachedAnchor g k hk) i := by
  change postReferenceNode (InputMixedDesc.sourceMap g) (evaluationRawMap (k.app X))
    (InputSpanParameterNodes.sourceIso g k hk)
    (InputCommutingSimplex.nodes (polynomial.map g) (projection.app Y)
      (projection.app X) g (projection.naturality g) (InputCommutingRawNodes.rawIndex i)) = _
  rw [InputCommutingRawNodes.raw_nodes]
  exact post_pre_node (InputMixedDesc.sourceMap g) (evaluationModel (op Y))
    (evaluationRawMap (k.app X)) (rawSource g) (rawNodes g)
    (evaluationComparisonIso (polynomial.map g ≫ projection.app Y))
    (InputSpanParameterNodes.sourceIso g k hk) i

private theorem rectangle_nodes (i : Fin 5) :
    InputChartReference.rawNode g k hk (ProjectionRectangleSquareRows.polynomialRow i) =
      prePostNodes (InputMixedDesc.sourceMap g) (evaluationModel (op Y))
        (evaluationRawMap (k.app X)) (rawSource g) (rawNodes g)
        (rectangleAnchor g k hk) i := by
  rw [GlobalRawBass.InputDescNodes.raw_node_evaluate,
    ProjectionRectangleSquareRows.polynomial_row_nodes]
  exact pre_post_node (InputMixedDesc.sourceMap g) (evaluationModel (op Y))
    (evaluationRawMap (k.app X)) (rawSource g) (rawNodes g)
    (ProjectionRectangleSquareRows.polynomialAnchor (projection.app Y) (k.app Y)
      (k.app X) (polynomial.map g) (laurent.map g) (k.naturality g)
      (GlobalRawBass.laurentProjection.app Y) (hk Y))
    (evaluationComparisonIso (laurent.map g ≫ GlobalRawBass.laurentProjection.app Y)) i

/-- The complete terminal projection node is the original terminal raw rectangle node. -/
theorem terminal_node :
    InputSpanParameterNodes.nodes g k hk 7 = InputChartReference.rawNode g k hk 17 :=
  (InputSpanParameterNodes.node_seven g k hk).trans
    (InputChartReference.prism_raw_nodes g k hk 2)

/-- All five raw polynomial nodes agree with their full original rectangle references. -/
theorem raw_nodes (i : Fin 5) :
    InputSpanParameterNodes.nodes g k hk (InputCommutingRawNodes.rawIndex i) =
      InputChartReference.rawNode g k hk (ProjectionRectangleSquareRows.polynomialRow i) :=
  prePost_families_match (InputMixedDesc.sourceMap g) (evaluationModel (op Y))
    (evaluationRawMap (k.app X)) (rawSource g) (rawNodes g)
    (attached_nodes g k hk) (rectangle_nodes g k hk) 4 (terminal_node g k hk) i

/-- The target of the attached evaluation column is the actual raw product terminal node. -/
theorem column_terminal_node :
    InputSpanParameterNodes.nodes g k hk 4 = InputRawChartProductNodes.nodes g k hk 9 := by
  exact (raw_nodes g k hk 2).trans
    ((GlobalRawBass.InputDescNodes.raw_node_evaluate g k hk 13).trans
      ((InputRawChartRows.chart_nodes g k hk 4).trans
        (InputRawChartProductNodes.terminal_nodes g k hk 4).symm))

/-- The entire original reverse-forward polynomial path retains its four primitive edges. -/
theorem raw_parameter (t : unitInterval) :
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
      (InputSpanParameterNodes.nodes g k hk)
      (StdSimplex.map InputCommutingRawNodes.rawIndex (NativeSquareFiveSimplex.parameter t)) =
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
      (InputChartReference.rawNode g k hk)
      (StdSimplex.map ProjectionRectangleSquareRows.polynomialRow
        (NativeSquareFiveSimplex.parameter t)) := by
  obtain ⟨i, z, hz⟩ := BassH1Support.square_path_in t
  rw [← hz]
  exact (CommonReferenceNerve.parameter_supported (InputMixedDesc.sourceMap g)
    (fun j => InputSpanParameterNodes.nodes g k hk (InputCommutingRawNodes.rawIndex j))
    (InputSpanParameterNodes.nodes g k hk) InputCommutingRawNodes.rawIndex (fun _ => rfl)
    (BassH1Support.edgeFace i)
    ((by decide : ∀ j : Fin 4,
      Monotone (InputCommutingRawNodes.rawIndex ∘ (BassH1Support.edgeFace j).toOrderHom)) i)
    z).trans
      (CommonReferenceNerve.parameter_supported (InputMixedDesc.sourceMap g)
        (fun j => InputSpanParameterNodes.nodes g k hk (InputCommutingRawNodes.rawIndex j))
        (InputChartReference.rawNode g k hk) ProjectionRectangleSquareRows.polynomialRow
        (fun j => (raw_nodes g k hk j).symm) (BassH1Support.edgeFace i)
        (ProjectionRectangleSquareRows.primitive_rows_monotone 1 i) z).symm

end Quillen.PerfectComplexes.GlobalBassEvaluation.InputSpanTargetNodes
