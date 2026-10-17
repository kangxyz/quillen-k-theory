/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialDirectIdentityNodes
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialDirectSquareReference
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPairDirectAction

/-! The two actual direct chart actions retain all five original endpoint nodes. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialDirectActionNodes
open CommonReferenceNerve
open scoped Simplicial Topology
open CoefficientBassRaw1PolynomialSourceCylinder
open CoefficientBassRaw1PolynomialDirectSquareReference
private theorem finite_parameter_node {V W T : Model.{u}}
    (E : V ⟶ W) (F : V ⟶ T) {q : ℕ} (f : Node E → Fin (q + 1) → Node F)
    (e : Node E) (w : StdSimplex ℝ (Fin (q + 1))) :
    FiniteParameter.parameter E F f
      (parameter E (fun _ : Fin 1 ↦ e) (StdSimplex.single 0), w) =
      parameter F (f e) w := by
  rw [FiniteParameter.parameter_characteristic, SimplexGrid.parameter_row, parameter_face]
  apply congrArg (fun N ↦ parameter F N w)
  funext j
  exact FiniteParameter.gridNodes_index E F f (fun _ : Fin 1 ↦ e) 0 j

variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The actual plus identity-source action has the original complete outer square nodes. -/
theorem plus_nodes (i : Fin 5) :
    CommonReferenceProduct.reanchor
      (isoWhiskerRight (CoefficientBassRaw1PolynomialPairDirectAction.polynomialIso P p q)
        (CoefficientBassSeedTargetChartAttachment.Jb P (b := c)).functor ≪≫
        (CoefficientBassSeedTargetChartAttachment.targetAnchor P (p ≫ q) (𝟙 (model P a))
          (reference P (underToLaurent R) a) (Iso.refl _)).symm)
      (CoefficientBassSeedTargetChartAttachment.movingNode P (p ≫ q) (𝟙 (model P a))
        (reference P (underToLaurent R) a) (Iso.refl _) (identityNode P a) i) =
      CoefficientBassRaw1PolynomialPairEndpointReferences.outerNodes
        P (underToLaurent R) p q i := by
  have h := CoefficientBassRaw1PolynomialDirectIdentityNodes.normalize_identity_node
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
    (CoefficientBassSeedTargetChartAttachment.M P (p ≫ q))
    (CoefficientBassSeedTargetChartAttachment.Jb P (b := c))
    (CoefficientBassSeedTargetChartAttachment.H P (p ≫ q))
    ((reference P (underToLaurent R) a) ≫ CoefficientBassSeedTargetChartAttachment.L P (p ≫ q))
    (CoefficientBassRaw1PolynomialRadialCaps.pairPolynomialIso P p q)
    (CoefficientBassSeedTargetChartAttachment.squareAnchor P (p ≫ q) (𝟙 (model P a))
      (reference P (underToLaurent R) a) (Iso.refl _))
    (CoefficientBassSeedTargetChartAttachment.rightIso P (p ≫ q))
    (directNodes P (underToLaurent R) p q i)
  have hn := normalized_direct_nodes P (underToLaurent R) p q i
  dsimp only [CoefficientBassRaw1PolynomialPairDirectAction.polynomialIso,
    CoefficientBassSeedTargetChartAttachment.targetAnchor,
    CoefficientBassSeedTargetChartAttachment.movingNode,
    identityNode, directNodes] at h ⊢
  apply h.trans
  dsimp only [directAnchor, terminalAnchor, CoefficientBassSeedTargetChartAttachment.rightIso,
    CoefficientBassRaw1PolynomialRadialCaps.pairPolynomialIso, directNodes,
    CoefficientBassRaw1PolynomialPairEndpointReferences.ca,
    CoefficientBassRaw1PolynomialPairEndpointReferences.cc,
    CoefficientBassRaw1PolynomialPausedChart.sheetReference,
    CoefficientBassSeedTargetChartAttachment.Jb, BassMWholeNerve.coefficientModel,
    laurentPlus] at hn ⊢
  simpa only [Iso.trans_symm] using hn

/-- The actual minus identity-source action has the original complete outer square nodes. -/
theorem minus_nodes (i : Fin 5) :
    CommonReferenceProduct.reanchor
      (isoWhiskerRight (CoefficientBassRaw1PolynomialPairDirectAction.polynomialIso P p q)
        (CoefficientBassNegativeTargetChartAttachment.Jb P (b := c)).functor ≪≫
        (CoefficientBassNegativeTargetChartAttachment.targetAnchor P (p ≫ q) (𝟙 (model P a))
          (reference P (underToLaurentInvert R) a) (Iso.refl _)).symm)
      (CoefficientBassNegativeTargetChartAttachment.movingNode P (p ≫ q) (𝟙 (model P a))
        (reference P (underToLaurentInvert R) a) (Iso.refl _) (identityNode P a) i) =
      CoefficientBassRaw1PolynomialPairEndpointReferences.outerNodes
        P (underToLaurentInvert R) p q i := by
  have h := CoefficientBassRaw1PolynomialDirectIdentityNodes.normalize_identity_node
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
    (CoefficientBassNegativeTargetChartAttachment.M P (p ≫ q))
    (CoefficientBassNegativeTargetChartAttachment.Jb P (b := c))
    (CoefficientBassNegativeTargetChartAttachment.H P (p ≫ q))
    ((reference P (underToLaurentInvert R) a) ≫
      CoefficientBassNegativeTargetChartAttachment.L P (p ≫ q))
    (CoefficientBassRaw1PolynomialRadialCaps.pairPolynomialIso P p q)
    (CoefficientBassNegativeTargetChartAttachment.squareAnchor P (p ≫ q) (𝟙 (model P a))
      (reference P (underToLaurentInvert R) a) (Iso.refl _))
    (CoefficientBassNegativeTargetChartAttachment.rightIso P (p ≫ q))
    (directNodes P (underToLaurentInvert R) p q i)
  have hn := normalized_direct_nodes P (underToLaurentInvert R) p q i
  dsimp only [CoefficientBassRaw1PolynomialPairDirectAction.polynomialIso,
    CoefficientBassNegativeTargetChartAttachment.targetAnchor,
    CoefficientBassNegativeTargetChartAttachment.movingNode,
    identityNode, directNodes] at h ⊢
  apply h.trans
  dsimp only [directAnchor, terminalAnchor, CoefficientBassNegativeTargetChartAttachment.rightIso,
    CoefficientBassRaw1PolynomialRadialCaps.pairPolynomialIso, directNodes,
    CoefficientBassRaw1PolynomialPairEndpointReferences.ca,
    CoefficientBassRaw1PolynomialPairEndpointReferences.cc,
    CoefficientBassRaw1PolynomialPausedChart.sheetReference,
    CoefficientBassNegativeTargetChartAttachment.Jb, BassMWholeNerve.coefficientModel,
    laurentMinus] at hn ⊢
  simpa only [Iso.trans_symm] using hn

/-- The complete direct plus chart path uses the unchanged original square clock. -/
theorem plus_family (t : unitInterval) :
    mapParameter (CommonReferenceProduct.reanchor
      (isoWhiskerRight (CoefficientBassRaw1PolynomialPairDirectAction.polynomialIso P p q)
        (CoefficientBassSeedTargetChartAttachment.Jb P (b := c)).functor ≪≫
        (CoefficientBassSeedTargetChartAttachment.targetAnchor P (p ≫ q) (𝟙 (model P a))
          (reference P (underToLaurent R) a) (Iso.refl _)).symm))
      (CoefficientBassSeedTargetChartAttachment.moving P (p ≫ q) (𝟙 (model P a))
        (reference P (underToLaurent R) a) (Iso.refl _) (identityParameter P a, t)) =
    parameter (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurent R) p q)
      (CoefficientBassRaw1PolynomialPairEndpointReferences.outerNodes P (underToLaurent R) p q)
      (NativeSquareFiveSimplex.parameter t) := by
  dsimp only [CoefficientBassSeedTargetChartAttachment.moving, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, identityParameter]
  rw [finite_parameter_node, mapParameter_parameter]
  apply congrArg (fun N ↦ parameter
    (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurent R) p q)
    N (NativeSquareFiveSimplex.parameter t))
  funext i
  exact plus_nodes P p q i

/-- The complete direct minus chart path uses the unchanged original square clock. -/
theorem minus_family (t : unitInterval) :
    mapParameter (CommonReferenceProduct.reanchor
      (isoWhiskerRight (CoefficientBassRaw1PolynomialPairDirectAction.polynomialIso P p q)
        (CoefficientBassNegativeTargetChartAttachment.Jb P (b := c)).functor ≪≫
        (CoefficientBassNegativeTargetChartAttachment.targetAnchor P (p ≫ q) (𝟙 (model P a))
          (reference P (underToLaurentInvert R) a) (Iso.refl _)).symm))
      (CoefficientBassNegativeTargetChartAttachment.moving P (p ≫ q) (𝟙 (model P a))
        (reference P (underToLaurentInvert R) a) (Iso.refl _) (identityParameter P a, t)) =
    parameter
      (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurentInvert R) p q)
      (CoefficientBassRaw1PolynomialPairEndpointReferences.outerNodes
        P (underToLaurentInvert R) p q)
      (NativeSquareFiveSimplex.parameter t) := by
  dsimp only [CoefficientBassNegativeTargetChartAttachment.moving, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, identityParameter]
  rw [finite_parameter_node, mapParameter_parameter]
  apply congrArg (fun N ↦ parameter
    (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurentInvert R) p q)
    N (NativeSquareFiveSimplex.parameter t))
  funext i
  exact minus_nodes P p q i

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialDirectActionNodes
