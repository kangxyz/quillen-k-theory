/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.BaseChange.Coefficients.Naturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveProductPauseOuterEndpoints

/-!
# Terminal chart outer face against the literal source-whiskered old cube

Only the terminal paused square is transferred through the three original rectangle supports.
The full reference equality includes the original polynomial endpoint sourceIso and total.
The varying three-surface is not transferred into the old 140-node family.
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

/-- The old paused chart inclusion, through all five original indexing stages. -/
def terminalOldChartIndex (inverse : Bool) : Fin 18 → Fin 140 :=
  BassMWholeOrder.oldIndex ∘ BassH1Order.oldIndex ∘ BassSupportOrder.oldIndex ∘
    BassReferenceMerge.chartFace.toOrderHom ∘
      (if inverse then BassOverlap.minusFace else BassOverlap.plusFace).toOrderHom

/-- Only these three whole primitive rectangles are asserted ordered. -/
theorem terminal_old_chart_monotone (inverse : Bool) (i : Fin 3) :
    Monotone (terminalOldChartIndex inverse ∘
      (BassPrimitiveSupport.rectangleFace i).toOrderHom) := by
  cases inverse
  · exact BassMWholeOrder.oldOldPlus_monotone i
  · exact BassMWholeOrder.oldOldMinus_monotone i

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c d : Under R} (u : a ⟶ b) (v : b ⟶ c) (w : c ⟶ d)

/-- The second polynomial endpoint retains its source equality and original total iso. -/
private theorem polynomial_endpoint_reference :
    (CoefficientSquareFamilies.polynomialNodes P u 4).2 =
      smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
        (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
          (polynomialUnderCoefficient R) u)) ≪≫
        boundedFlatNormalizedPullbackCompIso (polynomialProjection P b) (coefficientMap P u)) := by
  change NativeSquareFiveSimplex.sourceIso _ _ _ _ _ ≪≫
    BinaryNormalizationSimplex.total _ _ = _
  rw [smallIso_trans]
  exact congrArg (fun η ↦ η ≪≫ BinaryNormalizationSimplex.total
    (polynomialProjection P b) (coefficientMap P u))
      (smallIso_eqToIso (congrArg boundedFlatNormalizedPullback
        (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
          (polynomialUnderCoefficient R) u))).symm

/-- The full fixed-factor anchor is the canonical old precomposition/chart anchor.
No reference equality is assumed; the actual geometric factorizations prove it. -/
theorem chart_terminal_anchor
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d) :
    chartFixedSideAnchor P u v w α hd 1 =
      precompAnchor P u v w ≪≫ isoWhiskerLeft (coefficientModel P u).functor
        (BassOverlap.commonToChartReference P v w α hd) := by
  unfold chartFixedSideAnchor
  change chartProductAnchor P u v w α hd ≪≫
    isoWhiskerRight (CoefficientSquareFamilies.polynomialNodes P u 4).2
      (movingSquareSource P α v w).functor = _
  rw [polynomial_endpoint_reference, chartProductAnchor, precomp_anchor_small]
  erw [smallIso_postcomp, smallIso_precomp]
  have hraw := anchored_factorizations_strict
    (coefficientMap P (α.app d) ≫ coefficientMap P ((polynomialUnderFunctor R).map w) ≫
      coefficientMap P ((polynomialUnderFunctor R).map v))
    (polynomialProjection P b) (coefficientMap P u)
    (laurentProjection P d ≫ coefficientMap P w ≫ coefficientMap P v)
    (coefficientMap P ((polynomialUnderFunctor R).map u) ≫ polynomialProjection P a) _
    (BassOverlap.chart_total P v w α hd).symm
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
      (polynomialUnderCoefficient R) u)
    (precomp_total P u v w) (chartProductTotal P u v w α hd).symm
  simpa only [smallIso_trans, Iso.trans_assoc] using (congrArg smallIso hraw).symm

/-- Full Sigma equality, including the original endpoint and common-reference isomorphisms. -/
theorem chart_terminal_reference_nodes
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (i : Fin 18) :
    chartOuterNodes P u v w α hd 1 i =
      anchorNode (precompAnchor P u v w)
        (CommonReferenceNerve.precompNode (coefficientModel P u)
          (BassOverlap.chartOverlapNodes P v w α hd i)) := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  change chartFixedSideAnchor P u v w α hd 1 ≪≫
    isoWhiskerLeft (CoefficientSquareFamilies.polynomialNodes P u 4).1.functor
      (movingSquareNodes P α v w i).2 = _
  rw [chart_terminal_anchor]
  simp only [anchorNode, CommonReferenceNerve.precompNode, BassOverlap.chartOverlapNodes,
    isoWhiskerLeft_trans, Iso.trans_assoc]
  rfl

/-- All eighteen old chart nodes retain their full references through the original chain. -/
theorem terminal_old_plus_nodes (i : Fin 18) :
    precompNodes P u v w (terminalOldChartIndex false i) =
      chartOuterNodes P u v w (underToLaurent R) (laurentPlus_projection P d) 1 i := by
  rw [chart_terminal_reference_nodes]
  unfold precompNodes ModelSimplex.reanchorNodes
  change anchorNode (precompAnchor P u v w)
    (CommonReferenceNerve.precompNode (coefficientModel P u)
      (BassMWhole.nodes P v w (terminalOldChartIndex false i))) = _
  unfold terminalOldChartIndex
  simp only [Bool.false_eq_true, ite_false, Function.comp_apply]
  rw [BassMWhole.old_nodes, BassH1Merged.old_nodes, BassH0Merged.old_nodes,
    BassReferenceMerge.chart_nodes]
  apply congrArg (fun N : BassOverlap.Node P v w ↦
    anchorNode (precompAnchor P u v w)
      (CommonReferenceNerve.precompNode (coefficientModel P u) N))
  change BassBottomCommonFamily.nodes P v w
    (Fin.castAdd 15 (Fin.castAdd 18 i)) = _
  unfold BassBottomCommonFamily.nodes
  rw [Fin.addCases_left]
  unfold BassOverlap.nodes
  rw [Fin.addCases_left]

/-- All eighteen old chart nodes retain their full references through the original chain. -/
theorem terminal_old_minus_nodes (i : Fin 18) :
    precompNodes P u v w (terminalOldChartIndex true i) =
      chartOuterNodes P u v w (underToLaurentInvert R) (laurentMinus_projection P d) 1 i := by
  rw [chart_terminal_reference_nodes]
  unfold precompNodes ModelSimplex.reanchorNodes
  change anchorNode (precompAnchor P u v w)
    (CommonReferenceNerve.precompNode (coefficientModel P u)
      (BassMWhole.nodes P v w (terminalOldChartIndex true i))) = _
  unfold terminalOldChartIndex
  simp only [ite_true, Function.comp_apply]
  rw [BassMWhole.old_nodes, BassH1Merged.old_nodes, BassH0Merged.old_nodes,
    BassReferenceMerge.chart_nodes]
  apply congrArg (fun N : BassOverlap.Node P v w ↦
    anchorNode (precompAnchor P u v w)
      (CommonReferenceNerve.precompNode (coefficientModel P u) N))
  change BassBottomCommonFamily.nodes P v w
    (Fin.castAdd 15 (Fin.natAdd 18 i)) = _
  unfold BassBottomCommonFamily.nodes
  rw [Fin.addCases_left]
  unfold BassOverlap.nodes
  rw [Fin.addCases_right]

/-- The literal old cube chart face is restricted only on its three proved supports. -/
theorem terminal_old_plus_parameter {V W : Model.{u + 1}} (F : V ⟶ W)
    (N : Fin 140 → CommonReferenceNerve.Node F) (q s : unitInterval) :
    CommonReferenceNerve.parameter F N (BassMWhole.scalarCube.{u} ![q, s, 0]) =
      CommonReferenceNerve.parameter F (fun i ↦ N (terminalOldChartIndex false i))
        (DoubleSquareScalarPaths.coefficientPausedSquareParameter (q, s)) := by
  rw [BassMWhole.cube_left]
  change CommonReferenceNerve.parameter F N
    (StdSimplex.map BassMWholeOrder.oldIndex
      (StdSimplex.map BassH1Order.oldIndex
        (StdSimplex.map BassSupportOrder.oldIndex
          (StdSimplex.map BassReferenceMerge.chartFace.toOrderHom
            (StdSimplex.map BassOverlap.plusFace.toOrderHom
              (DoubleSquareScalarPaths.coefficientPausedSquareParameter (q, s))))))) = _
  simp only [← StdSimplex.map_comp]
  obtain ⟨i, z, hz⟩ := BassPrimitiveSupport.paused_chart_in (q, s)
  change StdSimplex.map (BassPrimitiveSupport.rectangleFace i).toOrderHom z =
    DoubleSquareScalarPaths.coefficientPausedSquareParameter (q, s) at hz
  rw [← hz]
  exact CommonReferenceNerve.parameter_supported F _ _ (terminalOldChartIndex false)
    (fun _ ↦ rfl) (BassPrimitiveSupport.rectangleFace i)
    (terminal_old_chart_monotone false i) z

/-- The literal old cube chart face is restricted only on its three proved supports. -/
theorem terminal_old_minus_parameter {V W : Model.{u + 1}} (F : V ⟶ W)
    (N : Fin 140 → CommonReferenceNerve.Node F) (q s : unitInterval) :
    CommonReferenceNerve.parameter F N (BassMWhole.scalarCube.{u} ![q, s, 1]) =
      CommonReferenceNerve.parameter F (fun i ↦ N (terminalOldChartIndex true i))
        (DoubleSquareScalarPaths.coefficientPausedSquareParameter (q, s)) := by
  rw [BassMWhole.cube_right]
  change CommonReferenceNerve.parameter F N
    (StdSimplex.map BassMWholeOrder.oldIndex
      (StdSimplex.map BassH1Order.oldIndex
        (StdSimplex.map BassSupportOrder.oldIndex
          (StdSimplex.map BassReferenceMerge.chartFace.toOrderHom
            (StdSimplex.map BassOverlap.minusFace.toOrderHom
              (DoubleSquareScalarPaths.coefficientPausedSquareParameter (q, s))))))) = _
  simp only [← StdSimplex.map_comp]
  obtain ⟨i, z, hz⟩ := BassPrimitiveSupport.paused_chart_in (q, s)
  change StdSimplex.map (BassPrimitiveSupport.rectangleFace i).toOrderHom z =
    DoubleSquareScalarPaths.coefficientPausedSquareParameter (q, s) at hz
  rw [← hz]
  exact CommonReferenceNerve.parameter_supported F _ _ (terminalOldChartIndex true)
    (fun _ ↦ rfl) (BassPrimitiveSupport.rectangleFace i)
    (terminal_old_chart_monotone true i) z

/-- The terminal outer chart is exactly the original paused prewhiskered chart face. -/
theorem chart_outer_terminal_plus (q s : unitInterval) :
    chartOuterSurface P u v w (underToLaurent R) (laurentPlus_projection P d) 1 ![1, q, s] =
      precompLift P u v w ![q, s, 0] := by
  change CommonReferenceNerve.parameter _
    (chartOuterNodes P u v w (underToLaurent R) (laurentPlus_projection P d) 1)
    (ChangedBoundaryPause.cube DoubleSquareScalarPaths.coefficientBoundaryParameter
      ![1, q, s]) =
    CommonReferenceNerve.parameter _ (precompNodes P u v w)
      (BassMWhole.scalarCube.{u} ![q, s, 0])
  rw [ChangedBoundaryPause.cube_one, terminal_old_plus_parameter]
  change CommonReferenceNerve.parameter _ _
    (DoubleSquareScalarPaths.coefficientPausedSquareParameter (q, s)) = _
  apply congrArg (fun N : Fin 18 → CommonReferenceNerve.Node
    (BassH0Diagram.reference P ((u ≫ v) ≫ w)) ↦
      CommonReferenceNerve.parameter _ N
        (DoubleSquareScalarPaths.coefficientPausedSquareParameter (q, s)))
  funext i
  exact (terminal_old_plus_nodes P u v w i).symm

/-- The terminal outer chart is exactly the original paused prewhiskered chart face. -/
theorem chart_outer_terminal_minus (q s : unitInterval) :
    chartOuterSurface P u v w (underToLaurentInvert R) (laurentMinus_projection P d) 1 ![1, q, s] =
      precompLift P u v w ![q, s, 1] := by
  change CommonReferenceNerve.parameter _
    (chartOuterNodes P u v w (underToLaurentInvert R) (laurentMinus_projection P d) 1)
    (ChangedBoundaryPause.cube DoubleSquareScalarPaths.coefficientBoundaryParameter
      ![1, q, s]) =
    CommonReferenceNerve.parameter _ (precompNodes P u v w)
      (BassMWhole.scalarCube.{u} ![q, s, 1])
  rw [ChangedBoundaryPause.cube_one, terminal_old_minus_parameter]
  change CommonReferenceNerve.parameter _ _
    (DoubleSquareScalarPaths.coefficientPausedSquareParameter (q, s)) = _
  apply congrArg (fun N : Fin 18 → CommonReferenceNerve.Node
    (BassH0Diagram.reference P ((u ≫ v) ≫ w)) ↦
      CommonReferenceNerve.parameter _ N
        (DoubleSquareScalarPaths.coefficientPausedSquareParameter (q, s)))
  funext i
  exact (terminal_old_minus_nodes P u v w i).symm

end Quillen.PerfectComplexes.BassMWholeNerve
