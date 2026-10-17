/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeInputPolynomialPlacement

/-! The two actual polynomial cells recover K on the original polynomial-square input. -/
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
namespace Quillen.PerfectComplexes.BassMWholeConeCarrier.InputPolynomial
open BassH0Merge CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
open BassProjectionPath.WholeReference
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)
local notation "E" => input P p q w
local notation "F" => InputPolynomial.reference P p q w
local notation "Jd" => targetProjection P (d := d)

/-- Place the positive polynomial carrier in the whole-reference cone using its positive vertex. -/
def plusPlace : C(carrier P p q w (underToLaurent R), FourEdge.scalarCone P d E) :=
  place P p q w (underToLaurent R) (laurentPlus_projection P d)
    (FourEdgeTree.plusVertex E Jd) (FourEdge.beta_plus P d E)

/-- Place the negative polynomial carrier in the whole-reference cone using its negative vertex. -/
def minusPlace : C(carrier P p q w (underToLaurentInvert R), FourEdge.scalarCone P d E) :=
  place P p q w (underToLaurentInvert R) (laurentMinus_projection P d)
    (FourEdgeTree.minusVertex E Jd) (FourEdge.beta_minus P d E)

theorem plusPlace_native (n : ℕ) (z : carrier P p q w (underToLaurent R))
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    FourEdge.coneEval P d E n (plusPlace P p q w z) x =
      (boundedFlatCoefficientBassPositiveConeInclusion P d).map n
        (CoefficientBassFiniteSourceSheetNative.evaluate F
          (BassMWholeNerve.coefficientModel P ((underToLaurent R).app d)) n z x) := by
  let J := BassMWholeNerve.coefficientModel P ((underToLaurent R).app d)
  have h : (fun z ↦ FourEdge.coneEval P d E n (plusPlace P p q w z) x) =
      (fun z ↦ (boundedFlatCoefficientBassPositiveConeInclusion P d).map n
        (CoefficientBassFiniteSourceSheetNative.evaluate F J n z x)) := by
    apply FourEdgeTree.SetDescent.funext (attaching F J (F ≫ J) (Iso.refl _)) (erase F)
    · rintro ⟨y, ⟨t⟩⟩
      dsimp only [plusPlace]
      rw [place_cylinder, FourEdge.coneEval_cylinder,
        CoefficientBassFiniteSourceSheetNative.evaluate_cylinder]
      change ReducedMappingCone.cylinder _ _
        ((boundedFlatCoefficientBassSquareComparison P d).map n)
          (t, FourEdgeTree.nativeEval E Jd n
            (SSet.toTop.map (FourEdgeTree.plusVertex E Jd) (polynomialPlacement P p q w y)) x) = _
      rw [FourEdgeTree.nativeEval_plus]
      dsimp only [FourEdgeTree.nativePlus, polynomialPlacement]
      rw [pointwise_reanchor]
      rfl
    · intro y
      change FourEdge.coneEval P d E n
        (plusPlace P p q w (SSet.toTop.map (left₀ F J (F ≫ J) (Iso.refl _)) y)) x =
          (boundedFlatCoefficientBassPositiveConeInclusion P d).map n
            (CoefficientBassFiniteSourceSheetNative.evaluate F J n
              (SSet.toTop.map (left₀ F J (F ≫ J) (Iso.refl _)) y) x)
      dsimp only [plusPlace]
      rw [place_laurent, FourEdge.coneEval_laurent,
        CoefficientBassFiniteSourceSheetNative.evaluate_laurent]
      dsimp only [laurentPlacement, FourEdge.laurentValue]
      rw [pointwise_reanchor]
      rfl
    · intro y
      have hy : y = (default : |tipSSet.{u+1}|) := Subsingleton.elim _ _
      subst y
      change FourEdge.coneEval P d E n
        (plusPlace P p q w (SSet.toTop.map (right₀ F J (F ≫ J) (Iso.refl _)) default)) x =
          (boundedFlatCoefficientBassPositiveConeInclusion P d).map n
            (CoefficientBassFiniteSourceSheetNative.evaluate F J n
              (SSet.toTop.map (right₀ F J (F ≫ J) (Iso.refl _)) default) x)
      dsimp only [plusPlace]
      rw [place_tip, FourEdge.coneEval_tip, CoefficientBassFiniteSourceSheetNative.evaluate_tip]
      exact ((boundedFlatCoefficientBassPositiveConeInclusion P d).map_point n).symm
  exact congrFun h z

theorem minusPlace_native (n : ℕ) (z : carrier P p q w (underToLaurentInvert R))
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    FourEdge.coneEval P d E n (minusPlace P p q w z) x =
      (boundedFlatCoefficientBassNegativeConeInclusion P d).map n
        (CoefficientBassFiniteSourceSheetNative.evaluate F
          (BassMWholeNerve.coefficientModel P ((underToLaurentInvert R).app d)) n z x) := by
  let J := BassMWholeNerve.coefficientModel P ((underToLaurentInvert R).app d)
  have h : (fun z ↦ FourEdge.coneEval P d E n (minusPlace P p q w z) x) =
      (fun z ↦ (boundedFlatCoefficientBassNegativeConeInclusion P d).map n
        (CoefficientBassFiniteSourceSheetNative.evaluate F J n z x)) := by
    apply FourEdgeTree.SetDescent.funext (attaching F J (F ≫ J) (Iso.refl _)) (erase F)
    · rintro ⟨y, ⟨t⟩⟩
      dsimp only [minusPlace]
      rw [place_cylinder, FourEdge.coneEval_cylinder,
        CoefficientBassFiniteSourceSheetNative.evaluate_cylinder]
      change ReducedMappingCone.cylinder _ _
        ((boundedFlatCoefficientBassSquareComparison P d).map n)
          (t, FourEdgeTree.nativeEval E Jd n
            (SSet.toTop.map (FourEdgeTree.minusVertex E Jd) (polynomialPlacement P p q w y)) x) = _
      rw [FourEdgeTree.nativeEval_minus]
      dsimp only [FourEdgeTree.nativeMinus, polynomialPlacement]
      rw [pointwise_reanchor]
      rfl
    · intro y
      change FourEdge.coneEval P d E n
        (minusPlace P p q w (SSet.toTop.map (left₀ F J (F ≫ J) (Iso.refl _)) y)) x =
          (boundedFlatCoefficientBassNegativeConeInclusion P d).map n
            (CoefficientBassFiniteSourceSheetNative.evaluate F J n
              (SSet.toTop.map (left₀ F J (F ≫ J) (Iso.refl _)) y) x)
      dsimp only [minusPlace]
      rw [place_laurent, FourEdge.coneEval_laurent,
        CoefficientBassFiniteSourceSheetNative.evaluate_laurent]
      dsimp only [laurentPlacement, FourEdge.laurentValue]
      rw [pointwise_reanchor]
      rfl
    · intro y
      have hy : y = (default : |tipSSet.{u+1}|) := Subsingleton.elim _ _
      subst y
      change FourEdge.coneEval P d E n
        (minusPlace P p q w (SSet.toTop.map (right₀ F J (F ≫ J) (Iso.refl _)) default)) x =
          (boundedFlatCoefficientBassNegativeConeInclusion P d).map n
            (CoefficientBassFiniteSourceSheetNative.evaluate F J n
              (SSet.toTop.map (right₀ F J (F ≫ J) (Iso.refl _)) default) x)
      dsimp only [minusPlace]
      rw [place_tip, FourEdge.coneEval_tip, CoefficientBassFiniteSourceSheetNative.evaluate_tip]
      exact ((boundedFlatCoefficientBassNegativeConeInclusion P d).map_point n).symm
  exact congrFun h z

/-- The positive input-polynomial family placed in the whole-reference scalar cone. -/
def plusFamily : C((I × I) × I, FourEdge.scalarCone P d E) :=
  (plusPlace P p q w).comp (family P p q w (underToLaurent R))

/-- The negative input-polynomial family placed in the whole-reference scalar cone. -/
def minusFamily : C((I × I) × I, FourEdge.scalarCone P d E) :=
  (minusPlace P p q w).comp (family P p q w (underToLaurentInvert R))

/-- The outer positive cells retain K and the original polynomial-square clock. -/
theorem plusFamily_native (n : ℕ) (r h t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    FourEdge.coneEval P d E n (plusFamily P p q w ((r, h), t)) x =
      (BassMWhole.coneComposition P q w).level n
        (r, ReducedMappingCone.cylinder _ _
          ((boundedFlatCoefficientBassSquareComparison P b).map n)
          (h, (HomotopyPushout.inl
            (boundedFlatPerfectPrespectrumMap (polynomialProjection P b))
            (boundedFlatPerfectPrespectrumMap (polynomialProjection P b))).map n
            ((boundedFlatCoefficientPolynomialSquareHomotopy P p).level n (t, x)))) := by
  dsimp only [plusFamily, ContinuousMap.comp_apply]
  rw [plusPlace_native, family_native]
  exact CoefficientBassRaw1PolynomialPairCone.plusValue_corrected P q w n r h _

/-- The inverse polynomial cell uses its own original chart and the same outer height. -/
theorem minusFamily_native (n : ℕ) (r h t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    FourEdge.coneEval P d E n (minusFamily P p q w ((r, h), t)) x =
      (BassMWhole.coneComposition P q w).level n
        (r, ReducedMappingCone.cylinder _ _
          ((boundedFlatCoefficientBassSquareComparison P b).map n)
          (h, (HomotopyPushout.inr
            (boundedFlatPerfectPrespectrumMap (polynomialProjection P b))
            (boundedFlatPerfectPrespectrumMap (polynomialProjection P b))).map n
            ((boundedFlatCoefficientPolynomialSquareHomotopy P p).level n (t, x)))) := by
  dsimp only [minusFamily, ContinuousMap.comp_apply]
  rw [minusPlace_native, family_native]
  exact CoefficientBassRaw1PolynomialPairCone.minusValue_corrected P q w n r h _

end Quillen.PerfectComplexes.BassMWholeConeCarrier.InputPolynomial
