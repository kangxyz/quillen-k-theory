/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialInputEvaluation
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassNegativeSupportMap
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveSupportMap
public import Quillen.Aglib.Topology.Path.HomotopyEvaluationTrans

/-! The original cone-composition cap on both genuine polynomial Bass-map inputs. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialInputCap
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (f : a ⟶ b) (p : b ⟶ c) (q : c ⟶ d)

/-- The complete Positive cap is evaluated in the original full Bass cone. -/
def plusValue (n : ℕ) (z : carrier P (underToLaurent R) f p q)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :=
  (boundedFlatCoefficientBassPositiveConeInclusion P d).map n
    (evaluate P (underToLaurent R) f p q n z x)

/-- The original positive square followed by its target inclusion. -/
abbrev plusChart := (boundedFlatCoefficientPlusSquareHomotopy P f).postcomp
  (mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P b)))
/-- The original positive target contraction on polynomial coefficient input. -/
abbrev plusContraction := Homotopy.precomp
  (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map f)))
  (mappingConeHomotopy (boundedFlatPerfectPrespectrumMap (laurentPlus P b)))

/-- The first original half keeps Laurent composition on the full chart-square input. -/
theorem plusValue_first (n : ℕ) (r t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    plusValue P f p q n (first P (underToLaurent R) f p q (r, t)) x =
      (BassMWhole.coneComposition P p q).level n
        (r, (boundedFlatCoefficientBassPositiveConeInclusion P b).map n
          ((plusChart P f).level n (t, x))) := by
  have h := first_native P (underToLaurent R) f p q n r t x
  dsimp only [plusValue]
  rw [h]
  have hd := congrArg (fun F ↦ F.map n
    ((boundedFlatCoefficientLaurentCompositionHomotopy P p q).level n
      (r, (boundedFlatCoefficientPlusSquareHomotopy P f).level n (t, x))))
    (boundedFlatCoefficientBassPositiveConeInclusion_inclusion P d)
  have hb := congrArg (fun F ↦ F.map n
    ((boundedFlatCoefficientPlusSquareHomotopy P f).level n (t, x)))
    (boundedFlatCoefficientBassPositiveConeInclusion_inclusion P b)
  exact hd.trans ((BassMWhole.cone_inclusion P p q n r
    ((boundedFlatCoefficientPlusSquareHomotopy P f).level n (t, x))).symm.trans
      (congrArg (fun y ↦ (BassMWhole.coneComposition P p q).level n (r, y)) hb.symm))

/-- The second original half retains the old corrected pair cap on the coefficient image. -/
theorem plusValue_last (n : ℕ) (r t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    plusValue P f p q n (last P (underToLaurent R) f p q (r, t)) x =
      (BassMWhole.coneComposition P p q).level n
        (r, (boundedFlatCoefficientBassPositiveConeInclusion P b).map n
          ((plusContraction P f).level n (t, x))) := by
  dsimp only [plusValue]
  rw [last_native]
  exact CoefficientBassRaw1PolynomialPairCone.plusValue_corrected P p q n r t
    ((boundedFlatPerfectPrespectrumMap
      (coefficientMap P ((polynomialUnderFunctor R).map f))).map n x)

/-- Both unchanged half clocks recover the actual original cap on the prescribed Bass map. -/
theorem plusValue_family (n : ℕ) (r h : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    plusValue P f p q n (family P (underToLaurent R) f p q (r, h)) x =
      (BassMWhole.coneComposition P p q).level n
        (r, (boundedFlatCoefficientBassConeMap P f).map n
          (ReducedMappingCone.cylinder _ _
            ((boundedFlatCoefficientBassSquareComparison P a).map n)
            (h, (HomotopyPushout.inl
              (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
              (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x))) := by
  have hsplit := ContinuousMap.Homotopy.Evaluation.trans_compare
    (firstSwap P (underToLaurent R) f p q) (lastSwap P (underToLaurent R) f p q)
    ((plusChart P f).levelHomotopy n).toHomotopy
    ((plusContraction P f).levelHomotopy n).toHomotopy
    (fun z ↦ plusValue P f p q n z x)
    (fun y ↦ (BassMWhole.coneComposition P p q).level n
      (r, (boundedFlatCoefficientBassPositiveConeInclusion P b).map n y)) r x
    (fun t ↦ plusValue_first P f p q n r t x)
    (fun t ↦ plusValue_last P f p q n r t x) h
  have hf := congrArg (fun F ↦ F.map n
    (ReducedMappingCone.cylinder _ _
      ((boundedFlatPerfectPrespectrumMap (laurentPlus P a)).map n) (h, x)))
    (boundedFlatCoefficientBassPositiveConeMap_factor P f)
  exact hsplit.trans (congrArg
    (fun y ↦ (BassMWhole.coneComposition P p q).level n (r, y)) hf.symm)

/-- The complete Negative cap is evaluated in the original full Bass cone. -/
def minusValue (n : ℕ) (z : carrier P (underToLaurentInvert R) f p q)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :=
  (boundedFlatCoefficientBassNegativeConeInclusion P d).map n
    (evaluate P (underToLaurentInvert R) f p q n z x)

/-- The original negative square followed by its target inclusion. -/
abbrev minusChart := (boundedFlatCoefficientMinusSquareHomotopy P f).postcomp
  (mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentMinus P b)))
/-- The original negative target contraction on polynomial coefficient input. -/
abbrev minusContraction := Homotopy.precomp
  (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map f)))
  (mappingConeHomotopy (boundedFlatPerfectPrespectrumMap (laurentMinus P b)))

/-- The first original half keeps Laurent composition on the full chart-square input. -/
theorem minusValue_first (n : ℕ) (r t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    minusValue P f p q n (first P (underToLaurentInvert R) f p q (r, t)) x =
      (BassMWhole.coneComposition P p q).level n
        (r, (boundedFlatCoefficientBassNegativeConeInclusion P b).map n
          ((minusChart P f).level n (t, x))) := by
  have h := first_native P (underToLaurentInvert R) f p q n r t x
  dsimp only [minusValue]
  rw [h]
  have hd := congrArg (fun F ↦ F.map n
    ((boundedFlatCoefficientLaurentCompositionHomotopy P p q).level n
      (r, (boundedFlatCoefficientMinusSquareHomotopy P f).level n (t, x))))
    (boundedFlatCoefficientBassNegativeConeInclusion_inclusion P d)
  have hb := congrArg (fun F ↦ F.map n
    ((boundedFlatCoefficientMinusSquareHomotopy P f).level n (t, x)))
    (boundedFlatCoefficientBassNegativeConeInclusion_inclusion P b)
  exact hd.trans ((BassMWhole.cone_inclusion P p q n r
    ((boundedFlatCoefficientMinusSquareHomotopy P f).level n (t, x))).symm.trans
      (congrArg (fun y ↦ (BassMWhole.coneComposition P p q).level n (r, y)) hb.symm))

/-- The second original half retains the old corrected pair cap on the coefficient image. -/
theorem minusValue_last (n : ℕ) (r t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    minusValue P f p q n (last P (underToLaurentInvert R) f p q (r, t)) x =
      (BassMWhole.coneComposition P p q).level n
        (r, (boundedFlatCoefficientBassNegativeConeInclusion P b).map n
          ((minusContraction P f).level n (t, x))) := by
  dsimp only [minusValue]
  rw [last_native]
  exact CoefficientBassRaw1PolynomialPairCone.minusValue_corrected P p q n r t
    ((boundedFlatPerfectPrespectrumMap
      (coefficientMap P ((polynomialUnderFunctor R).map f))).map n x)

/-- Both unchanged half clocks recover the actual original cap on the prescribed Bass map. -/
theorem minusValue_family (n : ℕ) (r h : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    minusValue P f p q n (family P (underToLaurentInvert R) f p q (r, h)) x =
      (BassMWhole.coneComposition P p q).level n
        (r, (boundedFlatCoefficientBassConeMap P f).map n
          (ReducedMappingCone.cylinder _ _
            ((boundedFlatCoefficientBassSquareComparison P a).map n)
            (h, (HomotopyPushout.inr
              (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
              (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x))) := by
  have hsplit := ContinuousMap.Homotopy.Evaluation.trans_compare
    (firstSwap P (underToLaurentInvert R) f p q) (lastSwap P (underToLaurentInvert R) f p q)
    ((minusChart P f).levelHomotopy n).toHomotopy
    ((minusContraction P f).levelHomotopy n).toHomotopy
    (fun z ↦ minusValue P f p q n z x)
    (fun y ↦ (BassMWhole.coneComposition P p q).level n
      (r, (boundedFlatCoefficientBassNegativeConeInclusion P b).map n y)) r x
    (fun t ↦ minusValue_first P f p q n r t x)
    (fun t ↦ minusValue_last P f p q n r t x) h
  have hf := congrArg (fun F ↦ F.map n
    (ReducedMappingCone.cylinder _ _
      ((boundedFlatPerfectPrespectrumMap (laurentMinus P a)).map n) (h, x)))
    (boundedFlatCoefficientBassNegativeConeMap_factor P f)
  exact hsplit.trans (congrArg
    (fun y ↦ (BassMWhole.coneComposition P p q).level n (r, y)) hf.symm)

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialInputCap
