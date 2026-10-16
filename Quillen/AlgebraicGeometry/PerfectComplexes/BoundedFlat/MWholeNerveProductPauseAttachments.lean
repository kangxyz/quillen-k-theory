/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveProductPause
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1InternalScalarJoins

/-!
# The fixed actual Laurent top seams and the changing raw chart-source face

Only the original primitive supports are used to identify the Laurent characteristic map.
The positive lower-half and inverse final-quarter coordinates stay distinct from the changing
coefficient-prism seams. These equations do not assemble the remaining outer boundary.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMWholeNerve
open BassReferenceMerge BassH0Merge BassH1Join

/-- The polynomial row is used only on its four original ordered primitive edges. -/
private def laurentChartEdge (inverse : Bool) (i : Fin 4) : ⦋1⦌ ⟶ ⦋30⦌ :=
  SimplexCategory.Hom.mk
    ⟨(productProjectionFace inverse).toOrderHom ∘ ProjectionRectangleSquareRows.polynomialRow ∘
      (BassH1Support.edgeFace i).toOrderHom,
      (by decide : ∀ (b : Bool) (j : Fin 4), Monotone
        ((productProjectionFace b).toOrderHom ∘ ProjectionRectangleSquareRows.polynomialRow ∘
          (BassH1Support.edgeFace j).toOrderHom)) inverse i⟩

/-- Only these eight original four-node inclusions are asserted monotone. -/
private def laurentChartProductEdge (inverse : Bool) (i : Fin 4) (j : Fin 2) :
    ⦋3⦌ ⟶ ⦋92⦌ :=
  SimplexCategory.Hom.mk
    ⟨laurentPolynomialSideIndex (productProjectionFace inverse) ∘
      (chartSideEdgeFace i j).toOrderHom, laurent_side_primitive_monotone inverse i j⟩

private theorem laurent_chart_edge_index (inverse : Bool) (i : Fin 4) (j : Fin 2)
    (k l : Fin 2) :
    (laurentChartProductEdge inverse i j).toOrderHom
      (Quillen.SimplexGrid.index 1 1 (k, l)) =
      Quillen.SimplexGrid.index 30 2
        ((laurentChartEdge inverse i).toOrderHom k,
          (BassMPrimitiveSupport.coefficientEdgeFace j).toOrderHom l) := by
  change laurentPolynomialSideIndex (productProjectionFace inverse)
    ((chartSideEdgeFace i j).toOrderHom (Quillen.SimplexGrid.index 1 1 (k, l))) = _
  rw [chart_side_edge_index]
  unfold laurentPolynomialSideIndex
  rw [Quillen.SimplexGrid.decode_index]
  rfl

/-- Whole Pl scalar restriction, proved through its original eight primitive products. -/
theorem laurent_chart_side_parameter (inverse : Bool) (s q : unitInterval) :
    Quillen.SimplexGrid.parameter.{u + 1} 30 2
      (StdSimplex.map ((productProjectionFace inverse).toOrderHom ∘
        ProjectionRectangleSquareRows.polynomialRow) (NativeSquareFiveSimplex.parameter s),
        binaryPath (k := 2) 0 1 2 q) =
      StdSimplex.map (laurentPolynomialSideIndex (productProjectionFace inverse))
        (Quillen.SimplexGrid.parameter.{u + 1} 4 2
          (NativeSquareFiveSimplex.parameter s, binaryPath (k := 2) 0 1 2 q)) := by
  obtain ⟨i, z, hz⟩ := BassH1Support.square_path_in s
  obtain ⟨j, y, hy⟩ := BassMPrimitiveSupport.coefficient_path_in q
  have hbase := Quillen.SimplexGrid.parameter_productMap.{u + 1}
    (BassH1Support.edgeFace i) (BassMPrimitiveSupport.coefficientEdgeFace j)
    (chartSideEdgeFace i j) (chart_side_edge_index i j) z y
  rw [hz, hy] at hbase
  have htarget := Quillen.SimplexGrid.parameter_productMap.{u + 1}
    (laurentChartEdge inverse i) (BassMPrimitiveSupport.coefficientEdgeFace j)
    (laurentChartProductEdge inverse i j) (laurent_chart_edge_index inverse i j) z y
  change Quillen.SimplexGrid.parameter.{u + 1} 30 2
    (StdSimplex.map (((productProjectionFace inverse).toOrderHom ∘
      ProjectionRectangleSquareRows.polynomialRow) ∘ (BassH1Support.edgeFace i).toOrderHom) z,
      StdSimplex.map (BassMPrimitiveSupport.coefficientEdgeFace j).toOrderHom y) = _ at htarget
  rw [StdSimplex.map_comp, hz, hy] at htarget
  refine htarget.trans ?_
  exact (StdSimplex.map_comp
    (Quillen.SimplexGrid.parameter.{u + 1} 1 1 (z, y) : StdSimplex ℝ (Fin 4))
    (chartSideEdgeFace i j).toOrderHom
    (laurentPolynomialSideIndex (productProjectionFace inverse))).trans
      (congrArg (StdSimplex.map (laurentPolynomialSideIndex (productProjectionFace inverse)))
        hbase.symm)

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c d : Under R} (u : a ⟶ b) (v : b ⟶ c) (w : c ⟶ d)

/-- The actual Pl top positive subface is the same original canonical characteristic map. -/
theorem laurent_prism_top_plus_parameter (q t : unitInterval) :
    laurentPrism P u v w ![q, 1, lower t] =
      CommonReferenceNerve.parameter _ (laurentPrismNodes P u v w)
        (StdSimplex.map (laurentPolynomialSideIndex BassH0Diagram.plusFace)
          (Quillen.SimplexGrid.parameter.{u + 1} 4 2
            (NativeSquareFiveSimplex.parameter t, binaryPath (k := 2) 0 1 2 q))) := by
  change CommonReferenceNerve.parameter _ (laurentPrismNodes P u v w)
    (Quillen.SimplexGrid.parameter.{u + 1} 30 2
      (BassH0Diagram.parameter (1, lower t), binaryPath (k := 2) 0 1 2 q)) = _
  rw [← BassH1Join.first_plus_parameter]
  exact congrArg (CommonReferenceNerve.parameter _ (laurentPrismNodes P u v w))
    (laurent_chart_side_parameter false t q)

/-- The inverse Pl top subface keeps the original final-quarter time and only path reversal. -/
theorem laurent_prism_top_minus_parameter (q t : unitInterval) :
    laurentPrism P u v w ![q, 1, upper (upper t)] =
      CommonReferenceNerve.parameter _ (laurentPrismNodes P u v w)
        (StdSimplex.map (laurentPolynomialSideIndex BassH0Diagram.minusFace)
          (Quillen.SimplexGrid.parameter.{u + 1} 4 2
            (NativeSquareFiveSimplex.parameter (unitInterval.symm t),
              binaryPath (k := 2) 0 1 2 q))) := by
  change CommonReferenceNerve.parameter _ (laurentPrismNodes P u v w)
    (Quillen.SimplexGrid.parameter.{u + 1} 30 2
      (BassH0Diagram.parameter (1, upper (upper t)), binaryPath (k := 2) 0 1 2 q)) = _
  rw [← BassH1Join.first_minus_parameter]
  exact congrArg (CommonReferenceNerve.parameter _ (laurentPrismNodes P u v w))
    (laurent_chart_side_parameter true (unitInterval.symm t) q)

/-- The whole positive Pl seam stays fixed in pause time at its original lower-half subface. -/
theorem chart_pause_plus_laurent_seam (a q t : unitInterval) :
    chartPause P u v w (underToLaurent R) (laurentPlus_projection P d) false
      ![a, q, 0, t] = laurentPrism P u v w ![q, 1, lower t] := by
  rw [chart_pause_target_side, chart_plus_composition_side]
  exact (laurent_prism_top_plus_parameter P u v w q t).symm

/-- The fixed inverse Pl seam retains the distinct final-quarter original coordinate. -/
theorem chart_pause_minus_laurent_seam (a q t : unitInterval) :
    chartPause P u v w (underToLaurentInvert R) (laurentMinus_projection P d) true
      ![a, q, 0, t] = laurentPrism P u v w ![q, 1, upper (upper t)] := by
  rw [chart_pause_target_side, chart_minus_composition_side]
  exact (laurent_prism_top_minus_parameter P u v w q t).symm

/-- The other chart side changes by rho, with the original raw 90-node reference family. -/
theorem chart_pause_source_side
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool) (a q t : unitInterval) :
    chartPause P u v w α hd inverse ![a, q, 1, t] =
      chartProductPrism P u v w α hd inverse ![ChangedBoundaryPause.time (a, q), 1, t] := by
  change CommonReferenceNerve.parameter _ (chartProductNodes P u v w α hd)
    (Quillen.SimplexGrid.parameter.{u + 1} 4 17
      (NativeSquareFiveSimplex.parameter (productPolynomialTime inverse t),
        ChangedBoundaryPause.cube DoubleSquareScalarPaths.coefficientBoundaryParameter
          ![a, q, 1])) =
    CommonReferenceNerve.parameter _ (chartProductNodes P u v w α hd)
      (Quillen.SimplexGrid.parameter.{u + 1} 4 17
        (NativeSquareFiveSimplex.parameter (productPolynomialTime inverse t),
          DoubleSquareScalarPaths.coefficientMovingSquareParameter
            (ChangedBoundaryPause.time (a, q), 1)))
  rw [ChangedBoundaryPause.cube_right, ChangedBoundaryPause.rightEdge_apply,
    CoefficientMovingSquareRows.moving_right]

end Quillen.PerfectComplexes.BassMWholeNerve
