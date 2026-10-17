/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialCompositeEndpoint
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPairEndpointReferences
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPairEndpointCells
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialCompositeReferenceAnchor

/-! Both complete composite chart rows and their unchanged original square clocks. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u v
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialCompositeActionNodes
open CommonReferenceNerve CoefficientBassRaw1PolynomialSourceCylinder

open CoefficientBassRaw1PolynomialCompositeEndpoint
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The actual first plus row is postcomposed by the second Laurent action. -/
def plusFirstNodes (i : Fin 5) :
    Node (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurent R) p q) :=
  CommonReferenceProduct.reanchor (plusLaurentIso P p q)
    (postcompNode (CoefficientBassSeedTargetChartAttachment.L P q)
      (CoefficientBassSeedTargetChartAttachment.movingNode P p (𝟙 (model P a))
        (reference P (underToLaurent R) a) (Iso.refl _) (identityNode P a) i))

/-- The actual second plus row uses the complete first polynomial target node. -/
def plusSecondNodes (i : Fin 5) :
    Node (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurent R) p q) :=
  CommonReferenceProduct.reanchor (plusLaurentIso P p q)
    (CoefficientBassSeedTargetChartAttachment.movingNode P q
      ((𝟙 (model P a)) ≫ CoefficientBassSeedTargetChartAttachment.M P p)
      ((reference P (underToLaurent R) a) ≫ CoefficientBassSeedTargetChartAttachment.L P p)
      (plusFirstAnchor P p)
      (postcompNode (CoefficientBassSeedTargetChartAttachment.M P p) (identityNode P a)) i)

/-- Every complete second plus node is exactly the original second endpoint row. -/
theorem plus_second_nodes (i : Fin 5) :
    plusSecondNodes P p q i =
      CoefficientBassRaw1PolynomialPairEndpointReferences.secondNodes
        P (underToLaurent R) p q i := by
  have h := normalize_second_node
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
    (CoefficientBassSeedTargetChartAttachment.M P p) (CoefficientBassSeedTargetChartAttachment.M
      P q)
    (CoefficientBassSeedTargetChartAttachment.Jb P (b := c))
      (CoefficientBassSeedTargetChartAttachment.H P q)
    (((reference P (underToLaurent R) a) ≫ CoefficientBassSeedTargetChartAttachment.L P p) ≫
      CoefficientBassSeedTargetChartAttachment.L P q)
    (BinaryNormalizationSimplex.total
      (coefficientMap P ((polynomialUnderFunctor R).map q))
      (coefficientMap P ((polynomialUnderFunctor R).map p)))
    (CoefficientBassSeedTargetChartAttachment.squareAnchor P q
      ((𝟙 (model P a)) ≫ CoefficientBassSeedTargetChartAttachment.M P p)
      ((reference P (underToLaurent R) a) ≫ CoefficientBassSeedTargetChartAttachment.L P p)
      (plusFirstAnchor P p)) (CoefficientBassSeedTargetChartAttachment.rightIso P q)
    (NativeSquareFiveSimplex.nodes
      (coefficientMap P ((laurentUnderFunctor R).map q)) (coefficientMap P ((underToLaurent
        R).app b))
      (coefficientMap P ((underToLaurent R).app c))
      (coefficientMap P ((polynomialUnderFunctor R).map q))
      (coefficientMap_naturality P (underToLaurent R) q) i)
  apply h.trans
  have ha := CoefficientBassRaw1PolynomialCompositeReferenceAnchor.second_anchor
    (coefficientMap P ((polynomialUnderFunctor R).map p))
    (coefficientMap P ((polynomialUnderFunctor R).map q))
    (coefficientMap P ((laurentUnderFunctor R).map q))
    (coefficientMap P ((underToLaurent R).app b)) (coefficientMap P ((underToLaurent R).app c))
    (coefficientMap_naturality P (underToLaurent R) q).symm
  have hb := congrArg (fun η ↦ BassH0Merge.preReferenceNode
    (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurent R) p q)
    (CoefficientBassSeedTargetChartAttachment.M P p) η
    (NativeSquareFiveSimplex.nodes
      (coefficientMap P ((laurentUnderFunctor R).map q))
      (coefficientMap P ((underToLaurent R).app b)) (coefficientMap P ((underToLaurent R).app c))
      (coefficientMap P ((polynomialUnderFunctor R).map q))
      (coefficientMap_naturality P (underToLaurent R) q) i)) ha
  dsimp only [CoefficientBassRaw1PolynomialPairEndpointReferences.secondNodes,
    CommonReferenceProduct.reanchor, BassH0Merge.preReferenceNode,
    CoefficientBassSeedTargetChartAttachment.rightIso, CoefficientBassSeedTargetChartAttachment.Jb,
    CoefficientBassSeedTargetChartAttachment.M, laurentPlus, BassMWholeNerve.coefficientModel,
    CoefficientBassRaw1PolynomialPausedChart.sheetAnchor,
    CoefficientBassRaw1PolynomialPausedChart.sheetReference,
    CoefficientBassRaw1PolynomialPairEndpointReferences.pp,
    CoefficientBassRaw1PolynomialPairEndpointReferences.pq,
    CoefficientBassRaw1PolynomialPairEndpointReferences.lq,
    CoefficientBassRaw1PolynomialPairEndpointReferences.cb,
    CoefficientBassRaw1PolynomialPairEndpointReferences.cc] at hb ⊢
  simpa only [Iso.trans_assoc] using hb

/-- The complete original first-target and second-source nodes are literally the same node. -/
theorem plus_middle_node : plusFirstNodes P p q 4 = plusSecondNodes P p q 2 := by
  dsimp only [plusFirstNodes, plusSecondNodes]
  rw [CoefficientBassSeedTargetChartAttachment.movingNode_one,
    CoefficientBassSeedTargetChartAttachment.movingNode_zero]

/-- Every complete first plus node is exactly the original first endpoint row. -/
theorem plus_first_nodes (i : Fin 5) :
    plusFirstNodes P p q i =
      CoefficientBassRaw1PolynomialPairEndpointReferences.firstNodes
        P (underToLaurent R) p q i := by
  have hm : plusFirstNodes P p q 4 =
      CoefficientBassRaw1PolynomialPairEndpointReferences.firstNodes P (underToLaurent R) p q 4
        := by
    rw [plus_middle_node, plus_second_nodes]
    exact (CoefficientBassRaw1PolynomialPairEndpointReferences.second_nodes
      P (underToLaurent R) p q 2).symm.trans
      (CoefficientBassRaw1PolynomialPairEndpointReferences.first_nodes
        P (underToLaurent R) p q 4)
  apply BassH1Join.post_families_match
    (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurent R) p q)
    (CoefficientBassSeedTargetChartAttachment.L P q) (CoefficientBassSeedTargetChartAttachment.H
      P p)
    (NativeSquareFiveSimplex.nodes
      (coefficientMap P ((laurentUnderFunctor R).map p)) (coefficientMap P ((underToLaurent
        R).app a))
      (coefficientMap P ((underToLaurent R).app b))
      (coefficientMap P ((polynomialUnderFunctor R).map p))
      (coefficientMap_naturality P (underToLaurent R) p))
    (ρ := plusLaurentIso P p q ≪≫
      isoWhiskerRight (CoefficientBassSeedTargetChartAttachment.squareAnchor P p (𝟙 (model P a))
        (reference P (underToLaurent R) a) (Iso.refl _))
          (CoefficientBassSeedTargetChartAttachment.L P q).functor ≪≫
      isoWhiskerRight (Functor.leftUnitor (CoefficientBassSeedTargetChartAttachment.H P p).functor)
        (CoefficientBassSeedTargetChartAttachment.L P q).functor)
    («σ» := CoefficientBassRaw1PolynomialPausedChart.sheetAnchor P (underToLaurent R) p q ≪≫
      CoefficientMovingSquareRows.firstAnchor
        (coefficientMap P ((polynomialUnderFunctor R).map p))
        (coefficientMap P ((polynomialUnderFunctor R).map q))
        (coefficientMap P ((laurentUnderFunctor R).map p))
        (coefficientMap P ((laurentUnderFunctor R).map q))
        (coefficientMap P ((underToLaurent R).app a)) (coefficientMap P ((underToLaurent R).app b))
        (coefficientMap P ((underToLaurent R).app c))
        (coefficientMap_naturality P (underToLaurent R) p).symm
        (coefficientMap_naturality P (underToLaurent R) q).symm)
    ?_ ?_ 4 hm i
  · intro j
    exact normalize_post_identity_node _ _ _ _ _ _ _
  · intro j
    simp only [CoefficientBassRaw1PolynomialPairEndpointReferences.firstNodes,
      CommonReferenceProduct.reanchor, BassH1Join.postReferenceNode, Iso.trans_assoc]

/-- The actual first minus row is postcomposed by the second Laurent action. -/
def minusFirstNodes (i : Fin 5) :
    Node (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurentInvert R) p q) :=
  CommonReferenceProduct.reanchor (minusLaurentIso P p q)
    (postcompNode (CoefficientBassNegativeTargetChartAttachment.L P q)
      (CoefficientBassNegativeTargetChartAttachment.movingNode P p (𝟙 (model P a))
        (reference P (underToLaurentInvert R) a) (Iso.refl _) (identityNode P a) i))

/-- The actual second minus row uses the complete first polynomial target node. -/
def minusSecondNodes (i : Fin 5) :
    Node (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurentInvert R) p q) :=
  CommonReferenceProduct.reanchor (minusLaurentIso P p q)
    (CoefficientBassNegativeTargetChartAttachment.movingNode P q
      ((𝟙 (model P a)) ≫ CoefficientBassNegativeTargetChartAttachment.M P p)
      ((reference P (underToLaurentInvert R) a) ≫ CoefficientBassNegativeTargetChartAttachment.L
        P p)
      (minusFirstAnchor P p)
      (postcompNode (CoefficientBassNegativeTargetChartAttachment.M P p) (identityNode P a)) i)

/-- Every complete second minus node is exactly the original second endpoint row. -/
theorem minus_second_nodes (i : Fin 5) :
    minusSecondNodes P p q i =
      CoefficientBassRaw1PolynomialPairEndpointReferences.secondNodes
        P (underToLaurentInvert R) p q i := by
  have h := normalize_second_node
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
    (CoefficientBassNegativeTargetChartAttachment.M P p)
      (CoefficientBassNegativeTargetChartAttachment.M P q)
    (CoefficientBassNegativeTargetChartAttachment.Jb P (b := c))
      (CoefficientBassNegativeTargetChartAttachment.H P q)
    (((reference P (underToLaurentInvert R) a) ≫ CoefficientBassNegativeTargetChartAttachment.L P
      p) ≫ CoefficientBassNegativeTargetChartAttachment.L P q)
    (BinaryNormalizationSimplex.total
      (coefficientMap P ((polynomialUnderFunctor R).map q))
      (coefficientMap P ((polynomialUnderFunctor R).map p)))
    (CoefficientBassNegativeTargetChartAttachment.squareAnchor P q
      ((𝟙 (model P a)) ≫ CoefficientBassNegativeTargetChartAttachment.M P p)
      ((reference P (underToLaurentInvert R) a) ≫ CoefficientBassNegativeTargetChartAttachment.L
        P p)
      (minusFirstAnchor P p)) (CoefficientBassNegativeTargetChartAttachment.rightIso P q)
    (NativeSquareFiveSimplex.nodes
      (coefficientMap P ((laurentUnderFunctor R).map q)) (coefficientMap P ((underToLaurentInvert
        R).app b))
      (coefficientMap P ((underToLaurentInvert R).app c))
      (coefficientMap P ((polynomialUnderFunctor R).map q))
      (coefficientMap_naturality P (underToLaurentInvert R) q) i)
  apply h.trans
  have ha := CoefficientBassRaw1PolynomialCompositeReferenceAnchor.second_anchor
    (coefficientMap P ((polynomialUnderFunctor R).map p))
    (coefficientMap P ((polynomialUnderFunctor R).map q))
    (coefficientMap P ((laurentUnderFunctor R).map q))
    (coefficientMap P ((underToLaurentInvert R).app b)) (coefficientMap P ((underToLaurentInvert
      R).app c))
    (coefficientMap_naturality P (underToLaurentInvert R) q).symm
  have hb := congrArg (fun η ↦ BassH0Merge.preReferenceNode
    (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurentInvert R) p q)
    (CoefficientBassNegativeTargetChartAttachment.M P p) η
    (NativeSquareFiveSimplex.nodes
      (coefficientMap P ((laurentUnderFunctor R).map q))
      (coefficientMap P ((underToLaurentInvert R).app b)) (coefficientMap P
        ((underToLaurentInvert R).app c))
      (coefficientMap P ((polynomialUnderFunctor R).map q))
      (coefficientMap_naturality P (underToLaurentInvert R) q) i)) ha
  dsimp only [CoefficientBassRaw1PolynomialPairEndpointReferences.secondNodes,
    CommonReferenceProduct.reanchor, BassH0Merge.preReferenceNode,
    CoefficientBassNegativeTargetChartAttachment.rightIso,
      CoefficientBassNegativeTargetChartAttachment.Jb,
    CoefficientBassNegativeTargetChartAttachment.M, laurentMinus, BassMWholeNerve.coefficientModel,
    CoefficientBassRaw1PolynomialPausedChart.sheetAnchor,
    CoefficientBassRaw1PolynomialPausedChart.sheetReference,
    CoefficientBassRaw1PolynomialPairEndpointReferences.pp,
    CoefficientBassRaw1PolynomialPairEndpointReferences.pq,
    CoefficientBassRaw1PolynomialPairEndpointReferences.lq,
    CoefficientBassRaw1PolynomialPairEndpointReferences.cb,
    CoefficientBassRaw1PolynomialPairEndpointReferences.cc] at hb ⊢
  simpa only [Iso.trans_assoc] using hb

/-- The complete original first-target and second-source nodes are literally the same node. -/
theorem minus_middle_node : minusFirstNodes P p q 4 = minusSecondNodes P p q 2 := by
  dsimp only [minusFirstNodes, minusSecondNodes]
  rw [CoefficientBassNegativeTargetChartAttachment.movingNode_one,
    CoefficientBassNegativeTargetChartAttachment.movingNode_zero]

/-- Every complete first minus node is exactly the original first endpoint row. -/
theorem minus_first_nodes (i : Fin 5) :
    minusFirstNodes P p q i =
      CoefficientBassRaw1PolynomialPairEndpointReferences.firstNodes
        P (underToLaurentInvert R) p q i := by
  have hm : minusFirstNodes P p q 4 =
      CoefficientBassRaw1PolynomialPairEndpointReferences.firstNodes P (underToLaurentInvert R) p
        q 4 := by
    rw [minus_middle_node, minus_second_nodes]
    exact (CoefficientBassRaw1PolynomialPairEndpointReferences.second_nodes
      P (underToLaurentInvert R) p q 2).symm.trans
      (CoefficientBassRaw1PolynomialPairEndpointReferences.first_nodes
        P (underToLaurentInvert R) p q 4)
  apply BassH1Join.post_families_match
    (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurentInvert R) p q)
    (CoefficientBassNegativeTargetChartAttachment.L P q)
      (CoefficientBassNegativeTargetChartAttachment.H P p)
    (NativeSquareFiveSimplex.nodes
      (coefficientMap P ((laurentUnderFunctor R).map p)) (coefficientMap P ((underToLaurentInvert
        R).app a))
      (coefficientMap P ((underToLaurentInvert R).app b))
      (coefficientMap P ((polynomialUnderFunctor R).map p))
      (coefficientMap_naturality P (underToLaurentInvert R) p))
    (ρ := minusLaurentIso P p q ≪≫
      isoWhiskerRight (CoefficientBassNegativeTargetChartAttachment.squareAnchor P p (𝟙 (model P a))
        (reference P (underToLaurentInvert R) a) (Iso.refl _))
          (CoefficientBassNegativeTargetChartAttachment.L P q).functor ≪≫
      isoWhiskerRight (Functor.leftUnitor (CoefficientBassNegativeTargetChartAttachment.H P
        p).functor)
        (CoefficientBassNegativeTargetChartAttachment.L P q).functor)
    («σ» := CoefficientBassRaw1PolynomialPausedChart.sheetAnchor P (underToLaurentInvert R) p q ≪≫
      CoefficientMovingSquareRows.firstAnchor
        (coefficientMap P ((polynomialUnderFunctor R).map p))
        (coefficientMap P ((polynomialUnderFunctor R).map q))
        (coefficientMap P ((laurentUnderFunctor R).map p))
        (coefficientMap P ((laurentUnderFunctor R).map q))
        (coefficientMap P ((underToLaurentInvert R).app a)) (coefficientMap P
          ((underToLaurentInvert R).app b))
        (coefficientMap P ((underToLaurentInvert R).app c))
        (coefficientMap_naturality P (underToLaurentInvert R) p).symm
        (coefficientMap_naturality P (underToLaurentInvert R) q).symm)
    ?_ ?_ 4 hm i
  · intro j
    exact normalize_post_identity_node _ _ _ _ _ _ _
  · intro j
    simp only [CoefficientBassRaw1PolynomialPairEndpointReferences.firstNodes,
      CommonReferenceProduct.reanchor, BassH1Join.postReferenceNode, Iso.trans_assoc]

private theorem finite_parameter_node {V W T : Model.{v}}
    (E : V ⟶ W) (F : V ⟶ T) {k : ℕ} (f : Node E → Fin (k + 1) → Node F)
    (e : Node E) (w : StdSimplex ℝ (Fin (k + 1))) :
    FiniteParameter.parameter E F f
      (parameter E (fun _ : Fin 1 ↦ e) (StdSimplex.single 0), w) =
      parameter F (f e) w := by
  rw [FiniteParameter.parameter_characteristic, SimplexGrid.parameter_row, parameter_face]
  apply congrArg (fun N ↦ parameter F N w)
  funext j
  exact FiniteParameter.gridNodes_index E F f (fun _ : Fin 1 ↦ e) 0 j

/-- The first composite plus chart track keeps all original five nodes and the exact clock. -/
theorem plus_first_family (t : I) :
    mapParameter (CommonReferenceProduct.reanchor (plusLaurentIso P p q))
      (mapParameter (postcompNode (CoefficientBassSeedTargetChartAttachment.L P q))
        (CoefficientBassSeedTargetChartAttachment.moving P p (𝟙 (model P a))
          (reference P (underToLaurent R) a) (Iso.refl _) (identityParameter P a, t))) =
    parameter (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurent R) p q)
      (CoefficientBassRaw1PolynomialPairEndpointReferences.firstNodes P (underToLaurent R) p q)
      (NativeSquareFiveSimplex.parameter t) := by
  dsimp only [CoefficientBassSeedTargetChartAttachment.moving, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, identityParameter]
  rw [finite_parameter_node, mapParameter_parameter, mapParameter_parameter]
  apply congrArg (fun N ↦ parameter
    (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurent R) p q)
    N (NativeSquareFiveSimplex.parameter t))
  funext i
  exact plus_first_nodes P p q i

/-- The second composite plus chart track keeps its independent original square clock. -/
theorem plus_second_family (t : I) :
    mapParameter (CommonReferenceProduct.reanchor (plusLaurentIso P p q))
      (CoefficientBassSeedTargetChartAttachment.moving P q
        ((𝟙 (model P a)) ≫ CoefficientBassSeedTargetChartAttachment.M P p)
        ((reference P (underToLaurent R) a) ≫ CoefficientBassSeedTargetChartAttachment.L P p)
        (plusFirstAnchor P p)
        (mapParameter (postcompNode (CoefficientBassSeedTargetChartAttachment.M P p))
          (identityParameter P a), t)) =
    parameter (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurent R) p q)
      (CoefficientBassRaw1PolynomialPairEndpointReferences.secondNodes P (underToLaurent R) p q)
      (NativeSquareFiveSimplex.parameter t) := by
  dsimp only [CoefficientBassSeedTargetChartAttachment.moving, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, identityParameter]
  rw [mapParameter_parameter, finite_parameter_node, mapParameter_parameter]
  apply congrArg (fun N ↦ parameter
    (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurent R) p q)
    N (NativeSquareFiveSimplex.parameter t))
  funext i
  exact plus_second_nodes P p q i

/-- The first composite minus chart track keeps all original five nodes and the exact clock. -/
theorem minus_first_family (t : I) :
    mapParameter (CommonReferenceProduct.reanchor (minusLaurentIso P p q))
      (mapParameter (postcompNode (CoefficientBassNegativeTargetChartAttachment.L P q))
        (CoefficientBassNegativeTargetChartAttachment.moving P p (𝟙 (model P a))
          (reference P (underToLaurentInvert R) a) (Iso.refl _) (identityParameter P a, t))) =
    parameter (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurentInvert R)
      p q)
      (CoefficientBassRaw1PolynomialPairEndpointReferences.firstNodes P (underToLaurentInvert R)
        p q)
      (NativeSquareFiveSimplex.parameter t) := by
  dsimp only [CoefficientBassNegativeTargetChartAttachment.moving, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, identityParameter]
  rw [finite_parameter_node, mapParameter_parameter, mapParameter_parameter]
  apply congrArg (fun N ↦ parameter
    (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurentInvert R) p q)
    N (NativeSquareFiveSimplex.parameter t))
  funext i
  exact minus_first_nodes P p q i

/-- The second composite minus chart track keeps its independent original square clock. -/
theorem minus_second_family (t : I) :
    mapParameter (CommonReferenceProduct.reanchor (minusLaurentIso P p q))
      (CoefficientBassNegativeTargetChartAttachment.moving P q
        ((𝟙 (model P a)) ≫ CoefficientBassNegativeTargetChartAttachment.M P p)
        ((reference P (underToLaurentInvert R) a) ≫
          CoefficientBassNegativeTargetChartAttachment.L P p)
        (minusFirstAnchor P p)
        (mapParameter (postcompNode (CoefficientBassNegativeTargetChartAttachment.M P p))
          (identityParameter P a), t)) =
    parameter (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurentInvert R)
      p q)
      (CoefficientBassRaw1PolynomialPairEndpointReferences.secondNodes P (underToLaurentInvert R)
        p q)
      (NativeSquareFiveSimplex.parameter t) := by
  dsimp only [CoefficientBassNegativeTargetChartAttachment.moving, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, identityParameter]
  rw [mapParameter_parameter, finite_parameter_node, mapParameter_parameter]
  apply congrArg (fun N ↦ parameter
    (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurentInvert R) p q)
    N (NativeSquareFiveSimplex.parameter t))
  funext i
  exact minus_second_nodes P p q i

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialCompositeActionNodes
