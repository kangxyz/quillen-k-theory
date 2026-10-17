/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialDirectActionNodes
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialDirectPolynomialEndpoint
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPairEndpointCells
public import Quillen.Topology.Path.ScalarRectangleConcatenation

/-! Exact two-half cells of the direct polynomial endpoint action. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
namespace CoefficientBassPolynomialSheetNormalization
/-- First-sheet normalization preserves the exact original cylinder height. -/
theorem map_cylinder {V W T : Model.{u}} (F F' : V ⟶ W) (J : W ⟶ T)
    (G : V ⟶ T) (ε : G.functor ≅ (F ≫ J).functor) (δ : F'.functor ≅ F.functor)
    (y : |parameterSSet F|) (t : I) :
    map F F' J G ε δ
      (DoubleCylinder.realizedCylinder (attaching F J G ε) (erase F) (y, ULift.up t)) =
    DoubleCylinder.realizedCylinder (attaching F' J (F' ≫ J) (Iso.refl _)) (erase F')
      (mapParameter (CommonReferenceProduct.reanchor δ) y, ULift.up t) :=
  DoubleCylinder.map_cylinder_apply _ _ _ _ _ _ _ _ _
end CoefficientBassPolynomialSheetNormalization
namespace CoefficientBassRaw1PolynomialPairDirectAction
open CoefficientBassRaw1PolynomialSourceCylinder
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The direct plus action preserves its original lower half. -/
theorem plusPath_lower (t : I) : plusPath P p q (lower t) =
    CoefficientBassRaw1PolynomialPairCone.laurent P (underToLaurent R) p q
      (parameter (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurent R) p q)
        (CoefficientBassRaw1PolynomialPairEndpointReferences.outerNodes P (underToLaurent R) p q)
        (NativeSquareFiveSimplex.parameter t)) := by
  let κ := CoefficientBassPolynomialSheetNormalization.map
    ((𝟙 (model P a)) ≫ CoefficientBassSeedTargetChartAttachment.M P (p ≫ q))
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
    (CoefficientBassSeedTargetChartAttachment.Jb P (b := c))
    ((reference P (underToLaurent R) a) ≫ CoefficientBassSeedTargetChartAttachment.L P (p ≫ q))
    (CoefficientBassSeedTargetChartAttachment.targetAnchor P (p ≫ q) (𝟙 (model P a))
      (reference P (underToLaurent R) a) (Iso.refl _)) (polynomialIso P p q)
  have hc := CoefficientBassPositiveTargetSingleSheet.firstMap_cylinder P (p ≫ q)
    (𝟙 (model P a)) (reference P (underToLaurent R) a) (Iso.refl _)
    (identityParameter P a) (lower t)
  have ht := ScalarRectangle.homotopy_lower
    (CoefficientBassPositiveTargetSingleSheet.chartTrack P (p ≫ q) (𝟙 (model P a))
      (reference P (underToLaurent R) a) (Iso.refl _) false)
    (CoefficientBassPositiveTargetSingleSheet.contraction P (p ≫ q) (𝟙 (model P a))
      (reference P (underToLaurent R) a) (Iso.refl _) false) t (identityParameter P a)
  have h := congrArg κ (hc.trans ht)
  have hm := CoefficientBassPolynomialSheetNormalization.map_laurent
    ((𝟙 (model P a)) ≫ CoefficientBassSeedTargetChartAttachment.M P (p ≫ q))
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
    (CoefficientBassSeedTargetChartAttachment.Jb P (b := c))
    ((reference P (underToLaurent R) a) ≫ CoefficientBassSeedTargetChartAttachment.L P (p ≫ q))
    (CoefficientBassSeedTargetChartAttachment.targetAnchor P (p ≫ q) (𝟙 (model P a))
      (reference P (underToLaurent R) a) (Iso.refl _)) (polynomialIso P p q)
    (CoefficientBassSeedTargetChartAttachment.moving P (p ≫ q) (𝟙 (model P a))
      (reference P (underToLaurent R) a) (Iso.refl _) (identityParameter P a, t))
  have hf := CoefficientBassRaw1PolynomialDirectActionNodes.plus_family P p q t
  exact h.trans (hm.trans (congrArg
    (CoefficientBassRaw1PolynomialPairCone.laurent P (underToLaurent R) p q) hf))

/-- The direct plus action preserves its original upper half. -/
theorem plusPath_upper (t : I) : plusPath P p q (upper t) =
    CoefficientBassRaw1PolynomialPairCone.cylinder P (underToLaurent R) p q
      (CoefficientBassRaw1PolynomialSourceAttachment.polynomialPausedPath P p q 0, t) := by
  let κ := CoefficientBassPolynomialSheetNormalization.map
    ((𝟙 (model P a)) ≫ CoefficientBassSeedTargetChartAttachment.M P (p ≫ q))
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
    (CoefficientBassSeedTargetChartAttachment.Jb P (b := c))
    ((reference P (underToLaurent R) a) ≫ CoefficientBassSeedTargetChartAttachment.L P (p ≫ q))
    (CoefficientBassSeedTargetChartAttachment.targetAnchor P (p ≫ q) (𝟙 (model P a))
      (reference P (underToLaurent R) a) (Iso.refl _)) (polynomialIso P p q)
  have hc := CoefficientBassPositiveTargetSingleSheet.firstMap_cylinder P (p ≫ q)
    (𝟙 (model P a)) (reference P (underToLaurent R) a) (Iso.refl _)
    (identityParameter P a) (upper t)
  have ht := ScalarRectangle.homotopy_upper
    (CoefficientBassPositiveTargetSingleSheet.chartTrack P (p ≫ q) (𝟙 (model P a))
      (reference P (underToLaurent R) a) (Iso.refl _) false)
    (CoefficientBassPositiveTargetSingleSheet.contraction P (p ≫ q) (𝟙 (model P a))
      (reference P (underToLaurent R) a) (Iso.refl _) false) t (identityParameter P a)
  have h := congrArg κ (hc.trans ht)
  have hm := CoefficientBassPolynomialSheetNormalization.map_cylinder
    ((𝟙 (model P a)) ≫ CoefficientBassSeedTargetChartAttachment.M P (p ≫ q))
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
    (CoefficientBassSeedTargetChartAttachment.Jb P (b := c))
    ((reference P (underToLaurent R) a) ≫ CoefficientBassSeedTargetChartAttachment.L P (p ≫ q))
    (CoefficientBassSeedTargetChartAttachment.targetAnchor P (p ≫ q) (𝟙 (model P a))
      (reference P (underToLaurent R) a) (Iso.refl _)) (polynomialIso P p q)
    (CoefficientBassPositiveTargetSingleSheet.polynomialMap P (p ≫ q) (𝟙 (model P a))
      (identityParameter P a)) t
  have hf := CoefficientBassRaw1PolynomialDirectPolynomialEndpoint.polynomial_parameter P p q
  exact h.trans (hm.trans (congrArg (fun y ↦
    CoefficientBassRaw1PolynomialPairCone.cylinder P (underToLaurent R) p q (y, t)) hf))

/-- The direct minus action preserves its original lower half. -/
theorem minusPath_lower (t : I) : minusPath P p q (lower t) =
    CoefficientBassRaw1PolynomialPairCone.laurent P (underToLaurentInvert R) p q
      (parameter
        (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurentInvert R) p q)
        (CoefficientBassRaw1PolynomialPairEndpointReferences.outerNodes
          P (underToLaurentInvert R) p q)
        (NativeSquareFiveSimplex.parameter t)) := by
  let κ := CoefficientBassPolynomialSheetNormalization.map
    ((𝟙 (model P a)) ≫ CoefficientBassNegativeTargetChartAttachment.M P (p ≫ q))
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
    (CoefficientBassNegativeTargetChartAttachment.Jb P (b := c))
    ((reference P (underToLaurentInvert R) a) ≫
      CoefficientBassNegativeTargetChartAttachment.L P (p ≫ q))
    (CoefficientBassNegativeTargetChartAttachment.targetAnchor P (p ≫ q) (𝟙 (model P a))
      (reference P (underToLaurentInvert R) a) (Iso.refl _)) (polynomialIso P p q)
  have hc := CoefficientBassNegativeTargetSingleSheet.firstMap_cylinder P (p ≫ q)
    (𝟙 (model P a)) (reference P (underToLaurentInvert R) a) (Iso.refl _)
    (identityParameter P a) (lower t)
  have ht := ScalarRectangle.homotopy_lower
    (CoefficientBassNegativeTargetSingleSheet.chartTrack P (p ≫ q) (𝟙 (model P a))
      (reference P (underToLaurentInvert R) a) (Iso.refl _) false)
    (CoefficientBassNegativeTargetSingleSheet.contraction P (p ≫ q) (𝟙 (model P a))
      (reference P (underToLaurentInvert R) a) (Iso.refl _) false) t (identityParameter P a)
  have h := congrArg κ (hc.trans ht)
  have hm := CoefficientBassPolynomialSheetNormalization.map_laurent
    ((𝟙 (model P a)) ≫ CoefficientBassNegativeTargetChartAttachment.M P (p ≫ q))
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
    (CoefficientBassNegativeTargetChartAttachment.Jb P (b := c))
    ((reference P (underToLaurentInvert R) a) ≫
      CoefficientBassNegativeTargetChartAttachment.L P (p ≫ q))
    (CoefficientBassNegativeTargetChartAttachment.targetAnchor P (p ≫ q) (𝟙 (model P a))
      (reference P (underToLaurentInvert R) a) (Iso.refl _)) (polynomialIso P p q)
    (CoefficientBassNegativeTargetChartAttachment.moving P (p ≫ q) (𝟙 (model P a))
      (reference P (underToLaurentInvert R) a) (Iso.refl _) (identityParameter P a, t))
  have hf := CoefficientBassRaw1PolynomialDirectActionNodes.minus_family P p q t
  exact h.trans (hm.trans (congrArg
    (CoefficientBassRaw1PolynomialPairCone.laurent P (underToLaurentInvert R) p q) hf))

/-- The direct minus action preserves its original upper half. -/
theorem minusPath_upper (t : I) : minusPath P p q (upper t) =
    CoefficientBassRaw1PolynomialPairCone.cylinder P (underToLaurentInvert R) p q
      (CoefficientBassRaw1PolynomialSourceAttachment.polynomialPausedPath P p q 0, t) := by
  let κ := CoefficientBassPolynomialSheetNormalization.map
    ((𝟙 (model P a)) ≫ CoefficientBassNegativeTargetChartAttachment.M P (p ≫ q))
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
    (CoefficientBassNegativeTargetChartAttachment.Jb P (b := c))
    ((reference P (underToLaurentInvert R) a) ≫
      CoefficientBassNegativeTargetChartAttachment.L P (p ≫ q))
    (CoefficientBassNegativeTargetChartAttachment.targetAnchor P (p ≫ q) (𝟙 (model P a))
      (reference P (underToLaurentInvert R) a) (Iso.refl _)) (polynomialIso P p q)
  have hc := CoefficientBassNegativeTargetSingleSheet.firstMap_cylinder P (p ≫ q)
    (𝟙 (model P a)) (reference P (underToLaurentInvert R) a) (Iso.refl _)
    (identityParameter P a) (upper t)
  have ht := ScalarRectangle.homotopy_upper
    (CoefficientBassNegativeTargetSingleSheet.chartTrack P (p ≫ q) (𝟙 (model P a))
      (reference P (underToLaurentInvert R) a) (Iso.refl _) false)
    (CoefficientBassNegativeTargetSingleSheet.contraction P (p ≫ q) (𝟙 (model P a))
      (reference P (underToLaurentInvert R) a) (Iso.refl _) false) t (identityParameter P a)
  have h := congrArg κ (hc.trans ht)
  have hm := CoefficientBassPolynomialSheetNormalization.map_cylinder
    ((𝟙 (model P a)) ≫ CoefficientBassNegativeTargetChartAttachment.M P (p ≫ q))
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
    (CoefficientBassNegativeTargetChartAttachment.Jb P (b := c))
    ((reference P (underToLaurentInvert R) a) ≫
      CoefficientBassNegativeTargetChartAttachment.L P (p ≫ q))
    (CoefficientBassNegativeTargetChartAttachment.targetAnchor P (p ≫ q) (𝟙 (model P a))
      (reference P (underToLaurentInvert R) a) (Iso.refl _)) (polynomialIso P p q)
    (CoefficientBassNegativeTargetSingleSheet.polynomialMap P (p ≫ q) (𝟙 (model P a))
      (identityParameter P a)) t
  have hf := CoefficientBassRaw1PolynomialDirectPolynomialEndpoint.polynomial_parameter P p q
  exact h.trans (hm.trans (congrArg (fun y ↦
    CoefficientBassRaw1PolynomialPairCone.cylinder P (underToLaurentInvert R) p q (y, t)) hf))

/-- The direct plus endpoint equals the entire prescribed initial cap path. -/
theorem plusPath_corrected_zero (s : I) :
    plusPath P p q s =
      CoefficientBassRaw1PolynomialPairCone.corrected P (underToLaurent R) p q (0, s) := by
  rw [CoefficientBassRaw1PolynomialPairCone.corrected_zero]
  rcases cover s with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · change plusPath P p q (lower t) =
      ((CoefficientBassRaw1PolynomialPairCone.firstSwap P (underToLaurent R) p q).trans
        (CoefficientBassRaw1PolynomialPairCone.lastSwap P (underToLaurent R) p q))
        (lower t, 0)
    rw [plusPath_lower, ScalarRectangle.homotopy_lower]
    change _ = CoefficientBassRaw1PolynomialPairCone.chartSquare P (underToLaurent R) p q (0, t)
    rw [CoefficientBassRaw1PolynomialPairCone.chartSquare_zero]
    apply congrArg (CoefficientBassRaw1PolynomialPairCone.laurent P (underToLaurent R) p q)
    apply congrArg (fun N ↦ parameter
      (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurent R) p q)
      N (NativeSquareFiveSimplex.parameter t))
    funext i
    exact (CoefficientBassRaw1PolynomialPairEndpointReferences.outer_nodes
      P (underToLaurent R) p q i).symm
  · change plusPath P p q (upper t) =
      ((CoefficientBassRaw1PolynomialPairCone.firstSwap P (underToLaurent R) p q).trans
        (CoefficientBassRaw1PolynomialPairCone.lastSwap P (underToLaurent R) p q))
        (upper t, 0)
    rw [plusPath_upper, ScalarRectangle.homotopy_upper]
    rfl

/-- The direct minus endpoint equals the entire prescribed initial cap path. -/
theorem minusPath_corrected_zero (s : I) :
    minusPath P p q s =
      CoefficientBassRaw1PolynomialPairCone.corrected P (underToLaurentInvert R) p q (0, s) := by
  rw [CoefficientBassRaw1PolynomialPairCone.corrected_zero]
  rcases cover s with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · change minusPath P p q (lower t) =
      ((CoefficientBassRaw1PolynomialPairCone.firstSwap P (underToLaurentInvert R) p q).trans
        (CoefficientBassRaw1PolynomialPairCone.lastSwap P (underToLaurentInvert R) p q))
        (lower t, 0)
    rw [minusPath_lower, ScalarRectangle.homotopy_lower]
    change _ = CoefficientBassRaw1PolynomialPairCone.chartSquare
      P (underToLaurentInvert R) p q (0, t)
    rw [CoefficientBassRaw1PolynomialPairCone.chartSquare_zero]
    apply congrArg (CoefficientBassRaw1PolynomialPairCone.laurent P (underToLaurentInvert R) p q)
    apply congrArg (fun N ↦ parameter
      (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurentInvert R) p q)
      N (NativeSquareFiveSimplex.parameter t))
    funext i
    exact (CoefficientBassRaw1PolynomialPairEndpointReferences.outer_nodes
      P (underToLaurentInvert R) p q i).symm
  · change minusPath P p q (upper t) =
      ((CoefficientBassRaw1PolynomialPairCone.firstSwap P (underToLaurentInvert R) p q).trans
        (CoefficientBassRaw1PolynomialPairCone.lastSwap P (underToLaurentInvert R) p q))
        (upper t, 0)
    rw [minusPath_upper, ScalarRectangle.homotopy_upper]
    rfl

end CoefficientBassRaw1PolynomialPairDirectAction
end Quillen.PerfectComplexes
