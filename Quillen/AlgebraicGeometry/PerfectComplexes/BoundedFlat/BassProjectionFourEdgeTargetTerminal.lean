/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeTargetTerminalCharts
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeTargetTerminalBetaEdges
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFourEdgeExt

/-! The entire original target beta seam on both genuine polynomial sectors and all four cells. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Target
open BassH0Merge CommonReferenceNerve
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
variable {V : Model.{u + 1}}
  (E : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
local notation "Ja" => normalizedMap (polynomialProjection P a)
local notation "U" => normalizedMap (coefficientMap P f)

/-- The whole plus polynomial chart has the exact terminal coefficient span value. -/
theorem chart_one_plus
    (y : |nerve (Codiscrete (CommonReferenceNerve.Node (polynomialReference P a E)))|) :
    chart P f E (underToLaurent R) (laurentPlus_projection P a) (y, 1) =
      mapParameter (terminalBoundaryNode P f E)
        (mapParameter (chartAttachmentNode P b (E ≫ U) (underToLaurent R)
          (laurentPlus_projection P b)) (TargetSpan.polynomialMap P f E y)) := by
  change FiniteParameter.parameter (polynomialReference P a E) (reference P f E)
    (chartNodes P f E (underToLaurent R) (laurentPlus_projection P a))
    (y, NativeSquareFiveSimplex.parameter 1) = _
  rw [Path.target, FiniteParameter.parameter_vertex,
    funext (chart_terminal_plus_node P f E)]
  obtain ⟨k, N, z, rfl⟩ := exists_parameter (polynomialReference P a E) y
  change mapParameter (fun M ↦ terminalBoundaryNode P f E
    (chartAttachmentNode P b (E ≫ U) (underToLaurent R) (laurentPlus_projection P b)
      (TargetSpan.polynomialMapNode P f E M))) (CommonReferenceNerve.parameter _ N z) =
    mapParameter (terminalBoundaryNode P f E)
      (mapParameter (chartAttachmentNode P b (E ≫ U) (underToLaurent R)
        (laurentPlus_projection P b))
        (mapParameter (TargetSpan.polynomialMapNode P f E) (CommonReferenceNerve.parameter _ N z)))
  simp only [mapParameter_parameter]

/-- The whole minus polynomial chart has the exact terminal coefficient span value. -/
theorem chart_one_minus
    (y : |nerve (Codiscrete (CommonReferenceNerve.Node (polynomialReference P a E)))|) :
    chart P f E (underToLaurentInvert R) (laurentMinus_projection P a) (y, 1) =
      mapParameter (terminalBoundaryNode P f E)
        (mapParameter (chartAttachmentNode P b (E ≫ U) (underToLaurentInvert R)
          (laurentMinus_projection P b)) (TargetSpan.polynomialMap P f E y)) := by
  change FiniteParameter.parameter (polynomialReference P a E) (reference P f E)
    (chartNodes P f E (underToLaurentInvert R) (laurentMinus_projection P a))
    (y, NativeSquareFiveSimplex.parameter 1) = _
  rw [Path.target, FiniteParameter.parameter_vertex,
    funext (chart_terminal_minus_node P f E)]
  obtain ⟨k, N, z, rfl⟩ := exists_parameter (polynomialReference P a E) y
  change mapParameter (fun M ↦ terminalBoundaryNode P f E
    (chartAttachmentNode P b (E ≫ U) (underToLaurentInvert R) (laurentMinus_projection P b)
      (TargetSpan.polynomialMapNode P f E M))) (CommonReferenceNerve.parameter _ N z) =
    mapParameter (terminalBoundaryNode P f E)
      (mapParameter (chartAttachmentNode P b (E ≫ U) (underToLaurentInvert R)
        (laurentMinus_projection P b))
        (mapParameter (TargetSpan.polynomialMapNode P f E) (CommonReferenceNerve.parameter _ N z)))
  simp only [mapParameter_parameter]

/-- The terminal H0 surface is exactly beta of the actual target span lift, on the whole tree. -/
theorem tree_terminal (z : FourEdgeTree.space E Ja) :
    tree P f E (z, 1) =
      mapParameter (terminalBoundaryNode P f E)
        (SSet.toTop.map (beta P b (E ≫ U)) (TargetSpan.treeMap P f E z)) := by
  suffices h : (fun z ↦ tree P f E (z, 1)) =
      (fun z ↦ mapParameter (terminalBoundaryNode P f E)
        (SSet.toTop.map (beta P b (E ≫ U)) (TargetSpan.treeMap P f E z))) from congrFun h z
  apply FourEdgeTree.funext_cells E Ja
  · intro y
    rw [tree_plus, TargetSpan.treeMap_plus]
    change chart P f E (underToLaurent R) (laurentPlus_projection P a) (y, 1) =
      mapParameter (terminalBoundaryNode P f E)
        (SSet.toTop.map (beta P b (E ≫ U))
          (SSet.toTop.map (FourEdgeTree.plusVertex (E ≫ U)
            (normalizedMap (polynomialProjection P b))) (TargetSpan.polynomialMap P f E y)))
    rw [← FourEdgeTree.realized_comp, beta_plus]
    exact chart_one_plus P f E y
  · intro y
    rw [tree_minus, TargetSpan.treeMap_minus]
    change chart P f E (underToLaurentInvert R) (laurentMinus_projection P a) (y, 1) =
      mapParameter (terminalBoundaryNode P f E)
        (SSet.toTop.map (beta P b (E ≫ U))
          (SSet.toTop.map (FourEdgeTree.minusVertex (E ≫ U)
            (normalizedMap (polynomialProjection P b))) (TargetSpan.polynomialMap P f E y)))
    rw [← FourEdgeTree.realized_comp, beta_minus]
    exact chart_one_minus P f E y
  · exact tree_terminal_edge12_beta P f E
  · exact tree_terminal_edge01_beta P f E
  · exact tree_terminal_edge03_beta P f E
  · exact tree_terminal_edge34_beta P f E

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Target
