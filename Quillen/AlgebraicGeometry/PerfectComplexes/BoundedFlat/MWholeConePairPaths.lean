/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConePairMap
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeInitialSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPairInitial

/-! The two prescribed pair-sheet edges retain the original A pause and initial-square halves. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMWholeConeCarrier.PairProjection
open CommonReferenceNerve CoefficientBassSpanCompositionReference
open CoefficientBassRaw1PolynomialSourceAttachment
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)
local notation "E" => inputReference P p q
local notation "J" => BassH0Merge.normalizedMap (polynomialProjection P c)

theorem polynomial_target_node
    (N : Node (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)) :
    polynomialNode P p q N = targetAttachmentNode P p q N := rfl

/-- All three full polynomial binary nodes have the original moving-square target anchor. -/
theorem polynomial_path (r : I) :
    polynomial P p q (coefficientPath P
      ((polynomialUnderFunctor R).map p) ((polynomialUnderFunctor R).map q) r) =
    polynomialSquare P p q (r, 0) := by
  rw [polynomialSquare_left]
  rfl

/-- The positive vertex carries the unchanged entire A path and its final half pause. -/
theorem plus_pausedPath (r : I) :
    vertex P p q (FourEdgeTree.plusVertex E J) (polynomialPausedPath P p q r) =
      treeComposition P p q (r, 0) := by
  rw [treeComposition_left]
  rcases cover r with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rw [polynomialPausedPath_lower, path_lower]
    exact congrArg (SSet.toTop.map (FourEdgeTree.plusVertex E J)) (polynomial_path P p q t)
  · rw [polynomialPausedPath_upper, path_upper]
    exact congrArg (SSet.toTop.map (FourEdgeTree.plusVertex E J)) (polynomial_path P p q 1)

/-- The inverse vertex keeps the same prescribed pause in its separate polynomial nerve. -/
theorem minus_pausedPath (r : I) :
    vertex P p q (FourEdgeTree.minusVertex E J) (polynomialPausedPath P p q r) =
      treeComposition P p q (r, 1) := by
  rw [treeComposition_right]
  rcases cover r with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rw [polynomialPausedPath_lower, path_lower]
    exact congrArg (SSet.toTop.map (FourEdgeTree.minusVertex E J)) (polynomial_path P p q t)
  · rw [polynomialPausedPath_upper, path_upper]
    exact congrArg (SSet.toTop.map (FourEdgeTree.minusVertex E J)) (polynomial_path P p q 1)

/-- Every height of the original positive target contraction maps to the original M side. -/
theorem plus_last (r s : I) :
    plus P p q (CoefficientBassRaw1PolynomialPairCone.last P (underToLaurent R) p q (r, s)) =
      last P p q (r, (s, 0)) := by
  dsimp only [plus, CoefficientBassRaw1PolynomialPairCone.last,
    CoefficientBassRaw1PolynomialPairCone.cylinder, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk]
  rw [map_cylinder, plus_pausedPath]
  rfl

/-- The inverse target contraction has the same original height at the other M side. -/
theorem minus_last (r s : I) :
    minus P p q (CoefficientBassRaw1PolynomialPairCone.last P
      (underToLaurentInvert R) p q (r, s)) = last P p q (r, (s, 1)) := by
  dsimp only [minus, CoefficientBassRaw1PolynomialPairCone.last,
    CoefficientBassRaw1PolynomialPairCone.cylinder, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk]
  rw [map_cylinder, minus_pausedPath]
  rfl

/-- The full positive initial null square keeps both original outer-height halves. -/
theorem plus_initial (r s : I) :
    plus P p q (CoefficientBassRaw1PolynomialPairCone.initial P
      (underToLaurent R) p q (r, s)) = initial P p q (r, (s, 0)) := by
  change plus P p q
    (((CoefficientBassRaw1PolynomialPairCone.firstSwap P (underToLaurent R) p q).trans
      (CoefficientBassRaw1PolynomialPairCone.lastSwap P (underToLaurent R) p q)) (s, r)) =
    ((firstSwap P p q).trans (lastSwap P p q)) (s, (r, 0))
  rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact plus_chartSquare P p q r _
  · exact plus_last P p q r _

/-- The inverse initial square uses its independent chart and the identical old two-half clock. -/
theorem minus_initial (r s : I) :
    minus P p q (CoefficientBassRaw1PolynomialPairCone.initial P
      (underToLaurentInvert R) p q (r, s)) = initial P p q (r, (s, 1)) := by
  change minus P p q
    (((CoefficientBassRaw1PolynomialPairCone.firstSwap P (underToLaurentInvert R) p q).trans
      (CoefficientBassRaw1PolynomialPairCone.lastSwap P (underToLaurentInvert R) p q)) (s, r)) =
    ((firstSwap P p q).trans (lastSwap P p q)) (s, (r, 1))
  rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact minus_chartSquare P p q r _
  · exact minus_last P p q r _

end Quillen.PerfectComplexes.BassMWholeConeCarrier.PairProjection
