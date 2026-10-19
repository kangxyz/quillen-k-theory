/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputRawDesc
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ProjectionRectangleSquareRows

/-!
# Complete raw chart rows on the mixed input descent boundary

The original five-node chart square has genuine polynomial source. Its actual projection
precomposition and evaluation retain every complete reference node. Both entire characteristic
rows and the original reverse-forward boundary paths agree before native evaluation.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.GlobalBassEvaluation.InputRawChartRows
open GlobalSectionChangeIndex BassH0Merge GlobalRawBass.InputDescSimplex
variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (k : laurent ⟶ polynomial)
  (hk : ∀ Z, k.app Z ≫ projection.app Z = GlobalRawBass.laurentProjection.app Z)

/-- The actual chart row is ordered in its original eighteen-node rectangle. -/
def rowFace : ⦋4⦌ ⟶ ⦋17⦌ :=
  SimplexCategory.Hom.mk ⟨ProjectionRectangleSquareRows.chartRow, by decide⟩

/-- The raw chart square starts on the actual polynomial scheme. -/
abbrev squareSource := NativeSquareFiveSimplex.source (laurent.map g) (k.app Y)

/-- Both original binary normalization routes and their actual naturality transport. -/
abbrev squareNodes := NativeSquareFiveSimplex.nodes
  (laurent.map g) (k.app Y) (k.app X) (polynomial.map g) (k.naturality g)

/-- The actual geometric projection equation supplies the whole raw chart-row anchor. -/
def projectionAnchor := ProjectionRectangleSquareRows.chartAnchor
  (projection.app Y) (k.app Y) (laurent.map g)
  (GlobalRawBass.laurentProjection.app Y) (hk Y)

/-- Projection precomposition followed by evaluation acts on the complete dependent node. -/
def projectedNode (N : CommonReferenceNerve.Node (squareSource g k)) :
    InputChartReference.Node g :=
  GlobalRawBass.InputDescNodes.evaluateNode g
    (preReferenceNode (reference g) (normalizedMap (projection.app Y))
      (projectionAnchor g k hk) N)

/-- Every original chart row node retains its complete mixed projection reference. -/
theorem chart_nodes (i : Fin 5) :
    GlobalRawBass.InputDescNodes.evaluateNode g
      (chartNodes g k hk (rowFace.toOrderHom i)) =
      projectedNode g k hk (squareNodes g k i) :=
  congrArg (GlobalRawBass.InputDescNodes.evaluateNode g)
    (ProjectionRectangleSquareRows.chart_row_nodes
      (projection.app Y) (k.app Y) (projection.app X) (k.app X)
      g (polynomial.map g) (laurent.map g) (projection.naturality g) (k.naturality g)
      (GlobalRawBass.laurentProjection.app Y) (hk Y) i)

/-- The full positive polynomial-source square row occurs in the actual descent diagram. -/
theorem plus_nodes (i : Fin 5) :
    mixedNodes g ((rowFace ≫ BassH0Diagram.plusFace).toOrderHom i) =
      projectedNode g plus GlobalRawBass.plus_projection (squareNodes g plus i) :=
  (congrArg (GlobalRawBass.InputDescNodes.evaluateNode g)
    (GlobalRawBass.InputDescSimplex.plus_nodes g (rowFace.toOrderHom i))).trans
    (chart_nodes g plus GlobalRawBass.plus_projection i)

/-- The inverse row keeps its separate original chart and the entire projection anchor. -/
theorem minus_nodes (i : Fin 5) :
    mixedNodes g ((rowFace ≫ BassH0Diagram.minusFace).toOrderHom i) =
      projectedNode g minus GlobalRawBass.minus_projection (squareNodes g minus i) :=
  (congrArg (GlobalRawBass.InputDescNodes.evaluateNode g)
    (GlobalRawBass.InputDescSimplex.minus_nodes g (rowFace.toOrderHom i))).trans
    (chart_nodes g minus GlobalRawBass.minus_projection i)

/-- The whole positive characteristic face agrees at every actual nerve point. -/
theorem plus_parameter (z : StdSimplex ℝ (Fin 5)) :
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) (mixedNodes g)
      (StdSimplex.map (rowFace ≫ BassH0Diagram.plusFace).toOrderHom z) =
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
      (fun i => projectedNode g plus GlobalRawBass.plus_projection (squareNodes g plus i)) z :=
  (CommonReferenceNerve.parameter_face (InputMixedDesc.sourceMap g) (mixedNodes g)
    (rowFace ≫ BassH0Diagram.plusFace) z).trans
    (congrArg (fun N => CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) N z)
      (funext (plus_nodes g)))

/-- The whole inverse characteristic face retains its distinct original geometric data. -/
theorem minus_parameter (z : StdSimplex ℝ (Fin 5)) :
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) (mixedNodes g)
      (StdSimplex.map (rowFace ≫ BassH0Diagram.minusFace).toOrderHom z) =
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
      (fun i => projectedNode g minus GlobalRawBass.minus_projection (squareNodes g minus i)) z :=
  (CommonReferenceNerve.parameter_face (InputMixedDesc.sourceMap g) (mixedNodes g)
    (rowFace ≫ BassH0Diagram.minusFace) z).trans
    (congrArg (fun N => CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) N z)
      (funext (minus_nodes g)))

/-- The complete positive descent edge is the unchanged original raw chart-square path. -/
theorem left_parameter (t : unitInterval) :
    InputRawDesc.parameter g (t, 0) =
      CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
        (fun i => projectedNode g plus GlobalRawBass.plus_projection (squareNodes g plus i))
        (NativeSquareFiveSimplex.parameter t) :=
  (InputRawDesc.parameter_left g t).trans
    ((congrArg (CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) (mixedNodes g))
      (ProjectionRectangleSquareRows.chart_parameter BassH0Diagram.plusFace t).symm).trans
      (plus_parameter g (NativeSquareFiveSimplex.parameter t)))

/-- The complete inverse descent edge retains the same reverse-forward subdivision. -/
theorem right_parameter (t : unitInterval) :
    InputRawDesc.parameter g (t, 1) =
      CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
        (fun i => projectedNode g minus GlobalRawBass.minus_projection (squareNodes g minus i))
        (NativeSquareFiveSimplex.parameter t) :=
  (InputRawDesc.parameter_right g t).trans
    ((congrArg (CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) (mixedNodes g))
      (ProjectionRectangleSquareRows.chart_parameter BassH0Diagram.minusFace t).symm).trans
      (minus_parameter g (NativeSquareFiveSimplex.parameter t)))

end Quillen.PerfectComplexes.GlobalBassEvaluation.InputRawChartRows
