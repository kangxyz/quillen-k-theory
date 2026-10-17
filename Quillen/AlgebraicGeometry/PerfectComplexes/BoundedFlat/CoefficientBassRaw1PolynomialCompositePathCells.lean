/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialCompositeActionNodes
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialCompositePolynomialEndpoint
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialDirectPathCells

/-! The exact three cells of the original composite polynomial action. -/
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
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialCompositeEndpoint
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
open CoefficientBassRaw1PolynomialSourceCylinder
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The composite plus action retains its literal first cell. -/
theorem plusPath_first (t : I) : plusPath P p q (lower t) =
    CoefficientBassRaw1PolynomialPairCone.laurent P (underToLaurent R) p q
      (parameter (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurent R) p q)
        (CoefficientBassRaw1PolynomialPairEndpointReferences.firstNodes P (underToLaurent R) p q)
        (NativeSquareFiveSimplex.parameter t)) := by
  let κ := CoefficientBassPolynomialSheetNormalization.map
    (((𝟙 (model P a)) ≫ CoefficientBassSeedTargetChartAttachment.M P p) ≫
      CoefficientBassSeedTargetChartAttachment.M P q)
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
    (CoefficientBassSeedTargetChartAttachment.Jb P (b := c))
    (((reference P (underToLaurent R) a) ≫ CoefficientBassSeedTargetChartAttachment.L P p) ≫
      CoefficientBassSeedTargetChartAttachment.L P q)
    (CoefficientBassSeedTargetChartAttachment.targetAnchor P q ((𝟙 (model P a)) ≫
      CoefficientBassSeedTargetChartAttachment.M P p)
      ((reference P (underToLaurent R) a) ≫ CoefficientBassSeedTargetChartAttachment.L P p)
        (plusFirstAnchor P p)) (polynomialIso P p q)
  let ψ := CoefficientBassPositiveTargetSingleSheet.firstMap P q ((𝟙 (model P a)) ≫
    CoefficientBassSeedTargetChartAttachment.M P p)
      ((reference P (underToLaurent R) a) ≫ CoefficientBassSeedTargetChartAttachment.L P p)
        (plusFirstAnchor P p)
  have hc := CoefficientBassPositiveTargetSingleSheet.firstMap_cylinder P p
    (𝟙 (model P a)) (reference P (underToLaurent R) a) (Iso.refl _)
    (identityParameter P a) (lower t)
  have ht := ScalarRectangle.homotopy_lower
    (CoefficientBassPositiveTargetSingleSheet.chartTrack P p (𝟙 (model P a))
      (reference P (underToLaurent R) a) (Iso.refl _) false)
    (CoefficientBassPositiveTargetSingleSheet.contraction P p (𝟙 (model P a))
      (reference P (underToLaurent R) a) (Iso.refl _) false) (t) (identityParameter P a)
  have h := congrArg (fun z ↦ κ (ψ z)) (hc.trans ht)
  have hq := CoefficientBassPositiveTargetSingleSheet.firstMap_laurent P q ((𝟙 (model P a)) ≫
    CoefficientBassSeedTargetChartAttachment.M P p)
      ((reference P (underToLaurent R) a) ≫ CoefficientBassSeedTargetChartAttachment.L P p)
        (plusFirstAnchor P p) (CoefficientBassSeedTargetChartAttachment.moving P p (𝟙 (model P a))
      (reference P (underToLaurent R) a) (Iso.refl _) (identityParameter P a, t))
  have hm := CoefficientBassPolynomialSheetNormalization.map_laurent
    (((𝟙 (model P a)) ≫ CoefficientBassSeedTargetChartAttachment.M P p) ≫
      CoefficientBassSeedTargetChartAttachment.M P q)
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
    (CoefficientBassSeedTargetChartAttachment.Jb P (b := c)) (((reference P (underToLaurent R) a)
      ≫ CoefficientBassSeedTargetChartAttachment.L P p) ≫
      CoefficientBassSeedTargetChartAttachment.L P q)
    (CoefficientBassSeedTargetChartAttachment.targetAnchor P q ((𝟙 (model P a)) ≫
      CoefficientBassSeedTargetChartAttachment.M P p)
      ((reference P (underToLaurent R) a) ≫ CoefficientBassSeedTargetChartAttachment.L P p)
        (plusFirstAnchor P p)) (polynomialIso P p q)
    (mapParameter (postcompNode (CoefficientBassSeedTargetChartAttachment.L P q))
      (CoefficientBassSeedTargetChartAttachment.moving P p (𝟙 (model P a))
      (reference P (underToLaurent R) a) (Iso.refl _) (identityParameter P a, t)))
  have hf := CoefficientBassRaw1PolynomialCompositeActionNodes.plus_first_family P p q t
  exact h.trans ((congrArg κ hq).trans (hm.trans (congrArg
    (CoefficientBassRaw1PolynomialPairCone.laurent P (underToLaurent R) p q) hf)))

/-- The composite plus action retains its literal second cell. -/
theorem plusPath_second (t : I) : plusPath P p q (upper (lower t)) =
    CoefficientBassRaw1PolynomialPairCone.laurent P (underToLaurent R) p q
      (parameter (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurent R) p q)
        (CoefficientBassRaw1PolynomialPairEndpointReferences.secondNodes P (underToLaurent R) p q)
        (NativeSquareFiveSimplex.parameter t)) := by
  let κ := CoefficientBassPolynomialSheetNormalization.map
    (((𝟙 (model P a)) ≫ CoefficientBassSeedTargetChartAttachment.M P p) ≫
      CoefficientBassSeedTargetChartAttachment.M P q)
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
    (CoefficientBassSeedTargetChartAttachment.Jb P (b := c))
    (((reference P (underToLaurent R) a) ≫ CoefficientBassSeedTargetChartAttachment.L P p) ≫
      CoefficientBassSeedTargetChartAttachment.L P q)
    (CoefficientBassSeedTargetChartAttachment.targetAnchor P q ((𝟙 (model P a)) ≫
      CoefficientBassSeedTargetChartAttachment.M P p)
      ((reference P (underToLaurent R) a) ≫ CoefficientBassSeedTargetChartAttachment.L P p)
        (plusFirstAnchor P p)) (polynomialIso P p q)
  let ψ := CoefficientBassPositiveTargetSingleSheet.firstMap P q ((𝟙 (model P a)) ≫
    CoefficientBassSeedTargetChartAttachment.M P p)
      ((reference P (underToLaurent R) a) ≫ CoefficientBassSeedTargetChartAttachment.L P p)
        (plusFirstAnchor P p)
  have hc := CoefficientBassPositiveTargetSingleSheet.firstMap_cylinder P p
    (𝟙 (model P a)) (reference P (underToLaurent R) a) (Iso.refl _)
    (identityParameter P a) (upper (lower t))
  have ht := ScalarRectangle.homotopy_upper
    (CoefficientBassPositiveTargetSingleSheet.chartTrack P p (𝟙 (model P a))
      (reference P (underToLaurent R) a) (Iso.refl _) false)
    (CoefficientBassPositiveTargetSingleSheet.contraction P p (𝟙 (model P a))
      (reference P (underToLaurent R) a) (Iso.refl _) false) (lower t) (identityParameter P a)
  have h := congrArg (fun z ↦ κ (ψ z)) (hc.trans ht)
  have hq := CoefficientBassPositiveTargetSingleSheet.firstMap_cylinder P q ((𝟙 (model P a)) ≫
    CoefficientBassSeedTargetChartAttachment.M P p)
      ((reference P (underToLaurent R) a) ≫ CoefficientBassSeedTargetChartAttachment.L P p)
        (plusFirstAnchor P p) (CoefficientBassPositiveTargetSingleSheet.polynomialMap P p (𝟙
        (model P a)) (identityParameter P a)) (lower t)
  have hqt := ScalarRectangle.homotopy_lower
    (CoefficientBassPositiveTargetSingleSheet.chartTrack P q ((𝟙 (model P a)) ≫
      CoefficientBassSeedTargetChartAttachment.M P p)
      ((reference P (underToLaurent R) a) ≫ CoefficientBassSeedTargetChartAttachment.L P p)
        (plusFirstAnchor P p) false)
    (CoefficientBassPositiveTargetSingleSheet.contraction P q ((𝟙 (model P a)) ≫
      CoefficientBassSeedTargetChartAttachment.M P p)
      ((reference P (underToLaurent R) a) ≫ CoefficientBassSeedTargetChartAttachment.L P p)
        (plusFirstAnchor P p) false) t (CoefficientBassPositiveTargetSingleSheet.polynomialMap P
        p (𝟙 (model P a)) (identityParameter P a))
  have hm := CoefficientBassPolynomialSheetNormalization.map_laurent
    (((𝟙 (model P a)) ≫ CoefficientBassSeedTargetChartAttachment.M P p) ≫
      CoefficientBassSeedTargetChartAttachment.M P q)
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
    (CoefficientBassSeedTargetChartAttachment.Jb P (b := c)) (((reference P (underToLaurent R) a)
      ≫ CoefficientBassSeedTargetChartAttachment.L P p) ≫
      CoefficientBassSeedTargetChartAttachment.L P q)
    (CoefficientBassSeedTargetChartAttachment.targetAnchor P q ((𝟙 (model P a)) ≫
      CoefficientBassSeedTargetChartAttachment.M P p)
      ((reference P (underToLaurent R) a) ≫ CoefficientBassSeedTargetChartAttachment.L P p)
        (plusFirstAnchor P p)) (polynomialIso P p q)
    (CoefficientBassSeedTargetChartAttachment.moving P q ((𝟙 (model P a)) ≫
      CoefficientBassSeedTargetChartAttachment.M P p)
      ((reference P (underToLaurent R) a) ≫ CoefficientBassSeedTargetChartAttachment.L P p)
        (plusFirstAnchor P p) ((CoefficientBassPositiveTargetSingleSheet.polynomialMap P p (𝟙
        (model P a)) (identityParameter P a)), t))
  have hf := CoefficientBassRaw1PolynomialCompositeActionNodes.plus_second_family P p q t
  exact h.trans ((congrArg κ (hq.trans hqt)).trans (hm.trans (congrArg
    (CoefficientBassRaw1PolynomialPairCone.laurent P (underToLaurent R) p q) hf)))

/-- The composite plus action retains its literal third cell. -/
theorem plusPath_third (t : I) : plusPath P p q (upper (upper t)) =
    CoefficientBassRaw1PolynomialPairCone.cylinder P (underToLaurent R) p q
      (CoefficientBassRaw1PolynomialSourceAttachment.polynomialPausedPath P p q 1, t) := by
  let κ := CoefficientBassPolynomialSheetNormalization.map
    (((𝟙 (model P a)) ≫ CoefficientBassSeedTargetChartAttachment.M P p) ≫
      CoefficientBassSeedTargetChartAttachment.M P q)
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
    (CoefficientBassSeedTargetChartAttachment.Jb P (b := c))
    (((reference P (underToLaurent R) a) ≫ CoefficientBassSeedTargetChartAttachment.L P p) ≫
      CoefficientBassSeedTargetChartAttachment.L P q)
    (CoefficientBassSeedTargetChartAttachment.targetAnchor P q ((𝟙 (model P a)) ≫
      CoefficientBassSeedTargetChartAttachment.M P p)
      ((reference P (underToLaurent R) a) ≫ CoefficientBassSeedTargetChartAttachment.L P p)
        (plusFirstAnchor P p)) (polynomialIso P p q)
  let ψ := CoefficientBassPositiveTargetSingleSheet.firstMap P q ((𝟙 (model P a)) ≫
    CoefficientBassSeedTargetChartAttachment.M P p)
      ((reference P (underToLaurent R) a) ≫ CoefficientBassSeedTargetChartAttachment.L P p)
        (plusFirstAnchor P p)
  have hc := CoefficientBassPositiveTargetSingleSheet.firstMap_cylinder P p
    (𝟙 (model P a)) (reference P (underToLaurent R) a) (Iso.refl _)
    (identityParameter P a) (upper (upper t))
  have ht := ScalarRectangle.homotopy_upper
    (CoefficientBassPositiveTargetSingleSheet.chartTrack P p (𝟙 (model P a))
      (reference P (underToLaurent R) a) (Iso.refl _) false)
    (CoefficientBassPositiveTargetSingleSheet.contraction P p (𝟙 (model P a))
      (reference P (underToLaurent R) a) (Iso.refl _) false) (upper t) (identityParameter P a)
  have h := congrArg (fun z ↦ κ (ψ z)) (hc.trans ht)
  have hq := CoefficientBassPositiveTargetSingleSheet.firstMap_cylinder P q ((𝟙 (model P a)) ≫
    CoefficientBassSeedTargetChartAttachment.M P p)
      ((reference P (underToLaurent R) a) ≫ CoefficientBassSeedTargetChartAttachment.L P p)
        (plusFirstAnchor P p) (CoefficientBassPositiveTargetSingleSheet.polynomialMap P p (𝟙
        (model P a)) (identityParameter P a)) (upper t)
  have hqt := ScalarRectangle.homotopy_upper
    (CoefficientBassPositiveTargetSingleSheet.chartTrack P q ((𝟙 (model P a)) ≫
      CoefficientBassSeedTargetChartAttachment.M P p)
      ((reference P (underToLaurent R) a) ≫ CoefficientBassSeedTargetChartAttachment.L P p)
        (plusFirstAnchor P p) false)
    (CoefficientBassPositiveTargetSingleSheet.contraction P q ((𝟙 (model P a)) ≫
      CoefficientBassSeedTargetChartAttachment.M P p)
      ((reference P (underToLaurent R) a) ≫ CoefficientBassSeedTargetChartAttachment.L P p)
        (plusFirstAnchor P p) false) t (CoefficientBassPositiveTargetSingleSheet.polynomialMap P
        p (𝟙 (model P a)) (identityParameter P a))
  have hm := CoefficientBassPolynomialSheetNormalization.map_cylinder
    (((𝟙 (model P a)) ≫ CoefficientBassSeedTargetChartAttachment.M P p) ≫
      CoefficientBassSeedTargetChartAttachment.M P q)
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
    (CoefficientBassSeedTargetChartAttachment.Jb P (b := c)) (((reference P (underToLaurent R) a)
      ≫ CoefficientBassSeedTargetChartAttachment.L P p) ≫
      CoefficientBassSeedTargetChartAttachment.L P q)
    (CoefficientBassSeedTargetChartAttachment.targetAnchor P q ((𝟙 (model P a)) ≫
      CoefficientBassSeedTargetChartAttachment.M P p)
      ((reference P (underToLaurent R) a) ≫ CoefficientBassSeedTargetChartAttachment.L P p)
        (plusFirstAnchor P p)) (polynomialIso P p q)
    (CoefficientBassPositiveTargetSingleSheet.polynomialMap P q ((𝟙 (model P a)) ≫
      CoefficientBassSeedTargetChartAttachment.M P p)
      (CoefficientBassPositiveTargetSingleSheet.polynomialMap P p (𝟙 (model P a))
      (identityParameter P a))) t
  have hf := CoefficientBassRaw1PolynomialCompositePolynomialEndpoint.polynomial_parameter P p q
  exact h.trans ((congrArg κ (hq.trans hqt)).trans (hm.trans (congrArg (fun y ↦
    CoefficientBassRaw1PolynomialPairCone.cylinder P (underToLaurent R) p q (y, t)) hf)))

/-- The composite minus action retains its literal first cell. -/
theorem minusPath_first (t : I) : minusPath P p q (lower t) =
    CoefficientBassRaw1PolynomialPairCone.laurent P (underToLaurentInvert R) p q
      (parameter (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurentInvert
        R) p q)
        (CoefficientBassRaw1PolynomialPairEndpointReferences.firstNodes P (underToLaurentInvert
          R) p q)
        (NativeSquareFiveSimplex.parameter t)) := by
  let κ := CoefficientBassPolynomialSheetNormalization.map
    (((𝟙 (model P a)) ≫ CoefficientBassNegativeTargetChartAttachment.M P p) ≫
      CoefficientBassNegativeTargetChartAttachment.M P q)
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
    (CoefficientBassNegativeTargetChartAttachment.Jb P (b := c))
    (((reference P (underToLaurentInvert R) a) ≫ CoefficientBassNegativeTargetChartAttachment.L P
      p) ≫ CoefficientBassNegativeTargetChartAttachment.L P q)
    (CoefficientBassNegativeTargetChartAttachment.targetAnchor P q ((𝟙 (model P a)) ≫
      CoefficientBassNegativeTargetChartAttachment.M P p)
      ((reference P (underToLaurentInvert R) a) ≫ CoefficientBassNegativeTargetChartAttachment.L
        P p) (minusFirstAnchor P p)) (polynomialIso P p q)
  let ψ := CoefficientBassNegativeTargetSingleSheet.firstMap P q ((𝟙 (model P a)) ≫
    CoefficientBassNegativeTargetChartAttachment.M P p)
      ((reference P (underToLaurentInvert R) a) ≫ CoefficientBassNegativeTargetChartAttachment.L
        P p) (minusFirstAnchor P p)
  have hc := CoefficientBassNegativeTargetSingleSheet.firstMap_cylinder P p
    (𝟙 (model P a)) (reference P (underToLaurentInvert R) a) (Iso.refl _)
    (identityParameter P a) (lower t)
  have ht := ScalarRectangle.homotopy_lower
    (CoefficientBassNegativeTargetSingleSheet.chartTrack P p (𝟙 (model P a))
      (reference P (underToLaurentInvert R) a) (Iso.refl _) false)
    (CoefficientBassNegativeTargetSingleSheet.contraction P p (𝟙 (model P a))
      (reference P (underToLaurentInvert R) a) (Iso.refl _) false) (t) (identityParameter P a)
  have h := congrArg (fun z ↦ κ (ψ z)) (hc.trans ht)
  have hq := CoefficientBassNegativeTargetSingleSheet.firstMap_laurent P q ((𝟙 (model P a)) ≫
    CoefficientBassNegativeTargetChartAttachment.M P p)
      ((reference P (underToLaurentInvert R) a) ≫ CoefficientBassNegativeTargetChartAttachment.L
        P p) (minusFirstAnchor P p) (CoefficientBassNegativeTargetChartAttachment.moving P p (𝟙
        (model P a))
      (reference P (underToLaurentInvert R) a) (Iso.refl _) (identityParameter P a, t))
  have hm := CoefficientBassPolynomialSheetNormalization.map_laurent
    (((𝟙 (model P a)) ≫ CoefficientBassNegativeTargetChartAttachment.M P p) ≫
      CoefficientBassNegativeTargetChartAttachment.M P q)
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
    (CoefficientBassNegativeTargetChartAttachment.Jb P (b := c)) (((reference P
      (underToLaurentInvert R) a) ≫ CoefficientBassNegativeTargetChartAttachment.L P p) ≫
      CoefficientBassNegativeTargetChartAttachment.L P q)
    (CoefficientBassNegativeTargetChartAttachment.targetAnchor P q ((𝟙 (model P a)) ≫
      CoefficientBassNegativeTargetChartAttachment.M P p)
      ((reference P (underToLaurentInvert R) a) ≫ CoefficientBassNegativeTargetChartAttachment.L
        P p) (minusFirstAnchor P p)) (polynomialIso P p q)
    (mapParameter (postcompNode (CoefficientBassNegativeTargetChartAttachment.L P q))
      (CoefficientBassNegativeTargetChartAttachment.moving P p (𝟙 (model P a))
      (reference P (underToLaurentInvert R) a) (Iso.refl _) (identityParameter P a, t)))
  have hf := CoefficientBassRaw1PolynomialCompositeActionNodes.minus_first_family P p q t
  exact h.trans ((congrArg κ hq).trans (hm.trans (congrArg
    (CoefficientBassRaw1PolynomialPairCone.laurent P (underToLaurentInvert R) p q) hf)))

/-- The composite minus action retains its literal second cell. -/
theorem minusPath_second (t : I) : minusPath P p q (upper (lower t)) =
    CoefficientBassRaw1PolynomialPairCone.laurent P (underToLaurentInvert R) p q
      (parameter (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurentInvert
        R) p q)
        (CoefficientBassRaw1PolynomialPairEndpointReferences.secondNodes P (underToLaurentInvert
          R) p q)
        (NativeSquareFiveSimplex.parameter t)) := by
  let κ := CoefficientBassPolynomialSheetNormalization.map
    (((𝟙 (model P a)) ≫ CoefficientBassNegativeTargetChartAttachment.M P p) ≫
      CoefficientBassNegativeTargetChartAttachment.M P q)
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
    (CoefficientBassNegativeTargetChartAttachment.Jb P (b := c))
    (((reference P (underToLaurentInvert R) a) ≫ CoefficientBassNegativeTargetChartAttachment.L P
      p) ≫ CoefficientBassNegativeTargetChartAttachment.L P q)
    (CoefficientBassNegativeTargetChartAttachment.targetAnchor P q ((𝟙 (model P a)) ≫
      CoefficientBassNegativeTargetChartAttachment.M P p)
      ((reference P (underToLaurentInvert R) a) ≫ CoefficientBassNegativeTargetChartAttachment.L
        P p) (minusFirstAnchor P p)) (polynomialIso P p q)
  let ψ := CoefficientBassNegativeTargetSingleSheet.firstMap P q ((𝟙 (model P a)) ≫
    CoefficientBassNegativeTargetChartAttachment.M P p)
      ((reference P (underToLaurentInvert R) a) ≫ CoefficientBassNegativeTargetChartAttachment.L
        P p) (minusFirstAnchor P p)
  have hc := CoefficientBassNegativeTargetSingleSheet.firstMap_cylinder P p
    (𝟙 (model P a)) (reference P (underToLaurentInvert R) a) (Iso.refl _)
    (identityParameter P a) (upper (lower t))
  have ht := ScalarRectangle.homotopy_upper
    (CoefficientBassNegativeTargetSingleSheet.chartTrack P p (𝟙 (model P a))
      (reference P (underToLaurentInvert R) a) (Iso.refl _) false)
    (CoefficientBassNegativeTargetSingleSheet.contraction P p (𝟙 (model P a))
      (reference P (underToLaurentInvert R) a) (Iso.refl _) false) (lower t) (identityParameter P a)
  have h := congrArg (fun z ↦ κ (ψ z)) (hc.trans ht)
  have hq := CoefficientBassNegativeTargetSingleSheet.firstMap_cylinder P q ((𝟙 (model P a)) ≫
    CoefficientBassNegativeTargetChartAttachment.M P p)
      ((reference P (underToLaurentInvert R) a) ≫ CoefficientBassNegativeTargetChartAttachment.L
        P p) (minusFirstAnchor P p) (CoefficientBassNegativeTargetSingleSheet.polynomialMap P p
        (𝟙 (model P a)) (identityParameter P a)) (lower t)
  have hqt := ScalarRectangle.homotopy_lower
    (CoefficientBassNegativeTargetSingleSheet.chartTrack P q ((𝟙 (model P a)) ≫
      CoefficientBassNegativeTargetChartAttachment.M P p)
      ((reference P (underToLaurentInvert R) a) ≫ CoefficientBassNegativeTargetChartAttachment.L
        P p) (minusFirstAnchor P p) false)
    (CoefficientBassNegativeTargetSingleSheet.contraction P q ((𝟙 (model P a)) ≫
      CoefficientBassNegativeTargetChartAttachment.M P p)
      ((reference P (underToLaurentInvert R) a) ≫ CoefficientBassNegativeTargetChartAttachment.L
        P p) (minusFirstAnchor P p) false) t
        (CoefficientBassNegativeTargetSingleSheet.polynomialMap P p (𝟙 (model P a))
        (identityParameter P a))
  have hm := CoefficientBassPolynomialSheetNormalization.map_laurent
    (((𝟙 (model P a)) ≫ CoefficientBassNegativeTargetChartAttachment.M P p) ≫
      CoefficientBassNegativeTargetChartAttachment.M P q)
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
    (CoefficientBassNegativeTargetChartAttachment.Jb P (b := c)) (((reference P
      (underToLaurentInvert R) a) ≫ CoefficientBassNegativeTargetChartAttachment.L P p) ≫
      CoefficientBassNegativeTargetChartAttachment.L P q)
    (CoefficientBassNegativeTargetChartAttachment.targetAnchor P q ((𝟙 (model P a)) ≫
      CoefficientBassNegativeTargetChartAttachment.M P p)
      ((reference P (underToLaurentInvert R) a) ≫ CoefficientBassNegativeTargetChartAttachment.L
        P p) (minusFirstAnchor P p)) (polynomialIso P p q)
    (CoefficientBassNegativeTargetChartAttachment.moving P q ((𝟙 (model P a)) ≫
      CoefficientBassNegativeTargetChartAttachment.M P p)
      ((reference P (underToLaurentInvert R) a) ≫ CoefficientBassNegativeTargetChartAttachment.L
        P p) (minusFirstAnchor P p) ((CoefficientBassNegativeTargetSingleSheet.polynomialMap P p
        (𝟙 (model P a)) (identityParameter P a)), t))
  have hf := CoefficientBassRaw1PolynomialCompositeActionNodes.minus_second_family P p q t
  exact h.trans ((congrArg κ (hq.trans hqt)).trans (hm.trans (congrArg
    (CoefficientBassRaw1PolynomialPairCone.laurent P (underToLaurentInvert R) p q) hf)))

/-- The composite minus action retains its literal third cell. -/
theorem minusPath_third (t : I) : minusPath P p q (upper (upper t)) =
    CoefficientBassRaw1PolynomialPairCone.cylinder P (underToLaurentInvert R) p q
      (CoefficientBassRaw1PolynomialSourceAttachment.polynomialPausedPath P p q 1, t) := by
  let κ := CoefficientBassPolynomialSheetNormalization.map
    (((𝟙 (model P a)) ≫ CoefficientBassNegativeTargetChartAttachment.M P p) ≫
      CoefficientBassNegativeTargetChartAttachment.M P q)
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
    (CoefficientBassNegativeTargetChartAttachment.Jb P (b := c))
    (((reference P (underToLaurentInvert R) a) ≫ CoefficientBassNegativeTargetChartAttachment.L P
      p) ≫ CoefficientBassNegativeTargetChartAttachment.L P q)
    (CoefficientBassNegativeTargetChartAttachment.targetAnchor P q ((𝟙 (model P a)) ≫
      CoefficientBassNegativeTargetChartAttachment.M P p)
      ((reference P (underToLaurentInvert R) a) ≫ CoefficientBassNegativeTargetChartAttachment.L
        P p) (minusFirstAnchor P p)) (polynomialIso P p q)
  let ψ := CoefficientBassNegativeTargetSingleSheet.firstMap P q ((𝟙 (model P a)) ≫
    CoefficientBassNegativeTargetChartAttachment.M P p)
      ((reference P (underToLaurentInvert R) a) ≫ CoefficientBassNegativeTargetChartAttachment.L
        P p) (minusFirstAnchor P p)
  have hc := CoefficientBassNegativeTargetSingleSheet.firstMap_cylinder P p
    (𝟙 (model P a)) (reference P (underToLaurentInvert R) a) (Iso.refl _)
    (identityParameter P a) (upper (upper t))
  have ht := ScalarRectangle.homotopy_upper
    (CoefficientBassNegativeTargetSingleSheet.chartTrack P p (𝟙 (model P a))
      (reference P (underToLaurentInvert R) a) (Iso.refl _) false)
    (CoefficientBassNegativeTargetSingleSheet.contraction P p (𝟙 (model P a))
      (reference P (underToLaurentInvert R) a) (Iso.refl _) false) (upper t) (identityParameter P a)
  have h := congrArg (fun z ↦ κ (ψ z)) (hc.trans ht)
  have hq := CoefficientBassNegativeTargetSingleSheet.firstMap_cylinder P q ((𝟙 (model P a)) ≫
    CoefficientBassNegativeTargetChartAttachment.M P p)
      ((reference P (underToLaurentInvert R) a) ≫ CoefficientBassNegativeTargetChartAttachment.L
        P p) (minusFirstAnchor P p) (CoefficientBassNegativeTargetSingleSheet.polynomialMap P p
        (𝟙 (model P a)) (identityParameter P a)) (upper t)
  have hqt := ScalarRectangle.homotopy_upper
    (CoefficientBassNegativeTargetSingleSheet.chartTrack P q ((𝟙 (model P a)) ≫
      CoefficientBassNegativeTargetChartAttachment.M P p)
      ((reference P (underToLaurentInvert R) a) ≫ CoefficientBassNegativeTargetChartAttachment.L
        P p) (minusFirstAnchor P p) false)
    (CoefficientBassNegativeTargetSingleSheet.contraction P q ((𝟙 (model P a)) ≫
      CoefficientBassNegativeTargetChartAttachment.M P p)
      ((reference P (underToLaurentInvert R) a) ≫ CoefficientBassNegativeTargetChartAttachment.L
        P p) (minusFirstAnchor P p) false) t
        (CoefficientBassNegativeTargetSingleSheet.polynomialMap P p (𝟙 (model P a))
        (identityParameter P a))
  have hm := CoefficientBassPolynomialSheetNormalization.map_cylinder
    (((𝟙 (model P a)) ≫ CoefficientBassNegativeTargetChartAttachment.M P p) ≫
      CoefficientBassNegativeTargetChartAttachment.M P q)
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
    (CoefficientBassNegativeTargetChartAttachment.Jb P (b := c)) (((reference P
      (underToLaurentInvert R) a) ≫ CoefficientBassNegativeTargetChartAttachment.L P p) ≫
      CoefficientBassNegativeTargetChartAttachment.L P q)
    (CoefficientBassNegativeTargetChartAttachment.targetAnchor P q ((𝟙 (model P a)) ≫
      CoefficientBassNegativeTargetChartAttachment.M P p)
      ((reference P (underToLaurentInvert R) a) ≫ CoefficientBassNegativeTargetChartAttachment.L
        P p) (minusFirstAnchor P p)) (polynomialIso P p q)
    (CoefficientBassNegativeTargetSingleSheet.polynomialMap P q ((𝟙 (model P a)) ≫
      CoefficientBassNegativeTargetChartAttachment.M P p)
      (CoefficientBassNegativeTargetSingleSheet.polynomialMap P p (𝟙 (model P a))
      (identityParameter P a))) t
  have hf := CoefficientBassRaw1PolynomialCompositePolynomialEndpoint.polynomial_parameter P p q
  exact h.trans ((congrArg κ (hq.trans hqt)).trans (hm.trans (congrArg (fun y ↦
    CoefficientBassRaw1PolynomialPairCone.cylinder P (underToLaurentInvert R) p q (y, t)) hf)))

/-- The composite plus path is the prescribed terminal cap word, with all three clocks. -/
theorem plusPath_corrected_one (s : I) : plusPath P p q s =
    CoefficientBassRaw1PolynomialPairCone.corrected P (underToLaurent R) p q (1, s) := by
  rw [CoefficientBassRaw1PolynomialPairCone.corrected_one]
  rcases cover s with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rw [plusPath_first, path_lower, CoefficientBassRaw1PolynomialPairCone.firstPath_row]
    apply congrArg (CoefficientBassRaw1PolynomialPairCone.laurent P (underToLaurent R) p q)
    apply congrArg (fun N ↦ parameter
      (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurent R) p q)
      N (NativeSquareFiveSimplex.parameter t))
    funext i
    exact (CoefficientBassRaw1PolynomialPairEndpointReferences.first_nodes
      P (underToLaurent R) p q i).symm
  · rw [path_upper]
    rcases cover t with ⟨v, rfl⟩ | ⟨v, rfl⟩
    · rw [plusPath_second, path_lower, CoefficientBassRaw1PolynomialPairCone.secondPath_row]
      apply congrArg (CoefficientBassRaw1PolynomialPairCone.laurent P (underToLaurent R) p q)
      apply congrArg (fun N ↦ parameter
        (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurent R) p q)
        N (NativeSquareFiveSimplex.parameter v))
      funext i
      exact (CoefficientBassRaw1PolynomialPairEndpointReferences.second_nodes
        P (underToLaurent R) p q i).symm
    · rw [plusPath_third, path_upper,
        CoefficientBassRaw1PolynomialPairCone.thirdPath_cylinder]

/-- The composite minus path is the prescribed terminal cap word, with all three clocks. -/
theorem minusPath_corrected_one (s : I) : minusPath P p q s =
    CoefficientBassRaw1PolynomialPairCone.corrected P (underToLaurentInvert R) p q (1, s) := by
  rw [CoefficientBassRaw1PolynomialPairCone.corrected_one]
  rcases cover s with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rw [minusPath_first, path_lower, CoefficientBassRaw1PolynomialPairCone.firstPath_row]
    apply congrArg (CoefficientBassRaw1PolynomialPairCone.laurent P (underToLaurentInvert R) p q)
    apply congrArg (fun N ↦ parameter
      (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurentInvert R) p q)
      N (NativeSquareFiveSimplex.parameter t))
    funext i
    exact (CoefficientBassRaw1PolynomialPairEndpointReferences.first_nodes
      P (underToLaurentInvert R) p q i).symm
  · rw [path_upper]
    rcases cover t with ⟨v, rfl⟩ | ⟨v, rfl⟩
    · rw [minusPath_second, path_lower, CoefficientBassRaw1PolynomialPairCone.secondPath_row]
      apply congrArg (CoefficientBassRaw1PolynomialPairCone.laurent P (underToLaurentInvert R) p q)
      apply congrArg (fun N ↦ parameter
        (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurentInvert R) p q)
        N (NativeSquareFiveSimplex.parameter v))
      funext i
      exact (CoefficientBassRaw1PolynomialPairEndpointReferences.second_nodes
        P (underToLaurentInvert R) p q i).symm
    · rw [minusPath_third, path_upper,
        CoefficientBassRaw1PolynomialPairCone.thirdPath_cylinder]

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialCompositeEndpoint
