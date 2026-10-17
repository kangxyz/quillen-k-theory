/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPostcomp
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPolynomialSheetNormalizationNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPairNative

/-! Exact original postcomposition of the polynomial caps in their fixed triple sheets. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialPostcomp
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)

/-- Native evaluation uses the literal first-sheet inclusion in the existing evaluator. -/
def evaluate (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R) (n : ℕ)
    (z : carrier P p q w β)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :=
  nativeEval (reference P p q w) (BassMWholeNerve.coefficientModel P (β.app d))
    (reference P p q w ≫ BassMWholeNerve.coefficientModel P (β.app d))
    (Iso.refl _) (Iso.refl _) n
    (SSet.toTop.map (left₁ (reference P p q w) (BassMWholeNerve.coefficientModel P (β.app d))
      (reference P p q w ≫ BassMWholeNerve.coefficientModel P (β.app d))
      (Iso.refl _) (Iso.refl _)) z) x

/-- The plus cap action is exactly the original coefficient map on every genuine input. -/
theorem plus_native (n : ℕ)
    (z : CoefficientBassRaw1PolynomialPairCone.carrier P (underToLaurent R) p q)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    (boundedFlatCoefficientBassPositiveConeInclusion P d).map n
      (evaluate P p q w (underToLaurent R) n (plus P p q w z) x) =
    (boundedFlatCoefficientBassConeMap P w).map n
      (CoefficientBassRaw1PolynomialPairCone.plusValue P p q n z x) := by
  let D := pair P p q
  let G := D ≫ CoefficientBassSeedTargetChartAttachment.Ja P (a := c)
  let η := CoefficientBassSeedTargetChartAttachment.targetAnchor P w D G (Iso.refl _)
  have hn := CoefficientBassPolynomialSheetNormalization.map_native
    (D ≫ CoefficientBassSeedTargetChartAttachment.M P w) (reference P p q w)
    (CoefficientBassSeedTargetChartAttachment.Jb P (b := d)) (G ≫
    CoefficientBassSeedTargetChartAttachment.L P w)
    η (polynomialIso P p q w) n
    (CoefficientBassPositiveTargetSingleSheet.firstMap P w D G (Iso.refl _) z) x
  have hf := CoefficientBassPositiveTargetSingleSheet.inclusion_firstMap P w D G (Iso.refl _) z
  have hv := congrArg (fun y ↦ nativeEval (D ≫ CoefficientBassSeedTargetChartAttachment.M P w)
    (CoefficientBassSeedTargetChartAttachment.Jb P (b := d)) (G ≫
    CoefficientBassSeedTargetChartAttachment.L P w)
    η η n y x) hf
  have he := hn.trans hv
  have hb := CoefficientBassSeedTargetCylinderNative.map_full_native P w D G (Iso.refl _)
    (Iso.refl _) n
    (SSet.toTop.map (left₁ D (CoefficientBassSeedTargetChartAttachment.Ja P (a := c)) G
      (Iso.refl _) (Iso.refl _)) z) x
  have hm := CoefficientBassSeedTargetCylinderMap.map_first P w D G (Iso.refl _) (Iso.refl _) z
  have ht := congrArg (fun y ↦ (boundedFlatCoefficientBassPositiveConeInclusion P d).map n
    (nativeEval (D ≫ CoefficientBassSeedTargetChartAttachment.M P w)
      (CoefficientBassSeedTargetChartAttachment.Jb P (b := d)) (G ≫
    CoefficientBassSeedTargetChartAttachment.L P w)
      η η n y x)) hm
  exact (congrArg ((boundedFlatCoefficientBassPositiveConeInclusion P d).map n) he).trans
    (hb.trans ht).symm

/-- The minus cap action is exactly the original coefficient map on every genuine input. -/
theorem minus_native (n : ℕ)
    (z : CoefficientBassRaw1PolynomialPairCone.carrier P (underToLaurentInvert R) p q)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    (boundedFlatCoefficientBassNegativeConeInclusion P d).map n
      (evaluate P p q w (underToLaurentInvert R) n (minus P p q w z) x) =
    (boundedFlatCoefficientBassConeMap P w).map n
      (CoefficientBassRaw1PolynomialPairCone.minusValue P p q n z x) := by
  let D := pair P p q
  let G := D ≫ CoefficientBassNegativeTargetChartAttachment.Ja P (a := c)
  let η := CoefficientBassNegativeTargetChartAttachment.targetAnchor P w D G (Iso.refl _)
  have hn := CoefficientBassPolynomialSheetNormalization.map_native
    (D ≫ CoefficientBassNegativeTargetChartAttachment.M P w) (reference P p q w)
    (CoefficientBassNegativeTargetChartAttachment.Jb P (b := d)) (G ≫
    CoefficientBassNegativeTargetChartAttachment.L P w)
    η (polynomialIso P p q w) n
    (CoefficientBassNegativeTargetSingleSheet.firstMap P w D G (Iso.refl _) z) x
  have hf := CoefficientBassNegativeTargetSingleSheet.inclusion_firstMap P w D G (Iso.refl _) z
  have hv := congrArg (fun y ↦ nativeEval (D ≫ CoefficientBassNegativeTargetChartAttachment.M P w)
    (CoefficientBassNegativeTargetChartAttachment.Jb P (b := d)) (G ≫
    CoefficientBassNegativeTargetChartAttachment.L P w)
    η η n y x) hf
  have he := hn.trans hv
  have hb := CoefficientBassNegativeTargetFirstNative.firstMap_full_native P w D G (Iso.refl
    _) (Iso.refl _) n z x
  exact (congrArg ((boundedFlatCoefficientBassNegativeConeInclusion P d).map n) he).trans hb.symm

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialPostcomp
