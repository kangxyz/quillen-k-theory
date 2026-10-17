/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeTargetTerminalPolynomialParameter
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeTargetSpanCells
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeOverlap

/-! The four full terminal beta seams with the original half-quarter-quarter span clock. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Target
open BassH0Merge CommonReferenceNerve ProjectionRectangleParameters

private theorem terminal_clock12 (t : I) :
    BassH0Diagram.parameter (1, FourEdgeTree.time12 t) =
      Ppath BassH0Diagram.plusFace (lower (unitInterval.symm t)) := by
  rw [BassH0Diagram.parameter_one]
  change ((Ppath BassH0Diagram.plusFace).trans _)
    (lower (unitInterval.symm (upper t))) = _
  rw [path_lower]
  congr 1
  apply Subtype.ext
  change 1 - ((t : ℝ) + 1) / 2 = (1 - (t : ℝ)) / 2
  ring

private theorem terminal_clock01 (t : I) :
    BassH0Diagram.parameter (1, FourEdgeTree.time01 t) =
      Ppath BassH0Diagram.plusFace (unitInterval.symm (lower t)) := by
  rw [BassH0Diagram.parameter_one]
  exact path_lower _ _ _

private theorem terminal_clock03 (t : I) :
    BassH0Diagram.parameter (1, FourEdgeTree.time03 t) =
      ((K BassH0Diagram.plusFace).symm.trans (K BassH0Diagram.minusFace)) t := by
  rw [BassH0Diagram.parameter_one]
  change ((Ppath BassH0Diagram.plusFace).trans _ ) (upper (lower t)) = _
  rw [path_upper, path_lower]

private theorem terminal_clock34 (t : I) :
    BassH0Diagram.parameter (1, FourEdgeTree.time34 t) =
      Ppath BassH0Diagram.minusFace (unitInterval.symm t) := by
  rw [BassH0Diagram.parameter_one]
  change ((Ppath BassH0Diagram.plusFace).trans _) (upper (upper t)) = _
  rw [path_upper, path_upper]
  rfl

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
variable {V : Model.{u + 1}}
  (E : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
local notation "Ja" => normalizedMap (polynomialProjection P a)
local notation "U" => normalizedMap (coefficientMap P f)

/-- The original edge 12 retains its full polynomial-square terminal attachment. -/
theorem tree_terminal_edge12_beta (y : |nerve (Codiscrete (CommonReferenceNerve.Node E))|)
    (t : I) :
    tree P f E (FourEdgeTree.realizedEdge (FourEdgeTree.edge12 E Ja) (y, t), 1) =
      mapParameter (terminalBoundaryNode P f E)
        (SSet.toTop.map (beta P b (E ≫ U))
          (TargetSpan.treeMap P f E
            (FourEdgeTree.realizedEdge (FourEdgeTree.edge12 E Ja) (y, t)))) := by
  rw [tree_edge12, TargetSpan.treeMap_edge12]
  change FiniteParameter.parameter E (reference P f E) (nodes P f E)
    (y, BassH0Diagram.parameter (1, FourEdgeTree.time12 t)) =
      mapParameter (terminalBoundaryNode P f E)
        (SSet.toTop.map (beta P b (E ≫ U))
          (SSet.toTop.map (FourEdgeTree.plusVertex (E ≫ U)
            (normalizedMap (polynomialProjection P b)))
              (TargetSpan.polynomialSquare P f E (y, lower (unitInterval.symm t)))))
  rw [terminal_clock12, ← FourEdgeTree.realized_comp, beta_plus]
  exact terminal_polynomial_plus_parameter P f E y (lower (unitInterval.symm t))

/-- The original edge 01 retains its full polynomial-square terminal attachment. -/
theorem tree_terminal_edge01_beta (y : |nerve (Codiscrete (CommonReferenceNerve.Node E))|)
    (t : I) :
    tree P f E (FourEdgeTree.realizedEdge (FourEdgeTree.edge01 E Ja) (y, t), 1) =
      mapParameter (terminalBoundaryNode P f E)
        (SSet.toTop.map (beta P b (E ≫ U))
          (TargetSpan.treeMap P f E
            (FourEdgeTree.realizedEdge (FourEdgeTree.edge01 E Ja) (y, t)))) := by
  rw [tree_edge01, TargetSpan.treeMap_edge01]
  change FiniteParameter.parameter E (reference P f E) (nodes P f E)
    (y, BassH0Diagram.parameter (1, FourEdgeTree.time01 t)) =
      mapParameter (terminalBoundaryNode P f E)
        (SSet.toTop.map (beta P b (E ≫ U))
          (SSet.toTop.map (FourEdgeTree.plusVertex (E ≫ U)
            (normalizedMap (polynomialProjection P b)))
              (TargetSpan.polynomialSquare P f E (y, unitInterval.symm (lower t)))))
  rw [terminal_clock01, ← FourEdgeTree.realized_comp, beta_plus]
  exact terminal_polynomial_plus_parameter P f E y (unitInterval.symm (lower t))

/-- The original edge 34 retains its full polynomial-square terminal attachment. -/
theorem tree_terminal_edge34_beta (y : |nerve (Codiscrete (CommonReferenceNerve.Node E))|)
    (t : I) :
    tree P f E (FourEdgeTree.realizedEdge (FourEdgeTree.edge34 E Ja) (y, t), 1) =
      mapParameter (terminalBoundaryNode P f E)
        (SSet.toTop.map (beta P b (E ≫ U))
          (TargetSpan.treeMap P f E
            (FourEdgeTree.realizedEdge (FourEdgeTree.edge34 E Ja) (y, t)))) := by
  rw [tree_edge34, TargetSpan.treeMap_edge34]
  change FiniteParameter.parameter E (reference P f E) (nodes P f E)
    (y, BassH0Diagram.parameter (1, FourEdgeTree.time34 t)) =
      mapParameter (terminalBoundaryNode P f E)
        (SSet.toTop.map (beta P b (E ≫ U))
          (SSet.toTop.map (FourEdgeTree.minusVertex (E ≫ U)
            (normalizedMap (polynomialProjection P b)))
              (TargetSpan.polynomialSquare P f E (y, unitInterval.symm t))))
  rw [terminal_clock34, ← FourEdgeTree.realized_comp, beta_minus]
  exact terminal_polynomial_minus_parameter P f E y (unitInterval.symm t)

/-- The middle quarter is the complete original target overlap after coefficient postcomposition. -/
theorem tree_terminal_edge03_beta (y : |nerve (Codiscrete (CommonReferenceNerve.Node E))|)
    (t : I) :
    tree P f E (FourEdgeTree.realizedEdge (FourEdgeTree.edge03 E Ja) (y, t), 1) =
      mapParameter (terminalBoundaryNode P f E)
        (SSet.toTop.map (beta P b (E ≫ U))
          (TargetSpan.treeMap P f E
            (FourEdgeTree.realizedEdge (FourEdgeTree.edge03 E Ja) (y, t)))) := by
  rw [tree_edge03, TargetSpan.treeMap_edge03]
  change FiniteParameter.parameter E (reference P f E) (nodes P f E)
    (y, BassH0Diagram.parameter (1, FourEdgeTree.time03 t)) =
      mapParameter (terminalBoundaryNode P f E)
        (SSet.toTop.map (beta P b (E ≫ U))
          (FourEdgeTree.overlap (E ≫ U) (normalizedMap (polynomialProjection P b))
            (mapParameter (postcompNode U) y, t)))
  rw [terminal_clock03, beta_overlap]
  exact terminal_whole_parameter P f E y t

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Target
