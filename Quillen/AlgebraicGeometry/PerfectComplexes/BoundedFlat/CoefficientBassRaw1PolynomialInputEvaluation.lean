/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialInputCap
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCutOpenPrecompNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPairCorrectedNative

/-! Exact evaluation of the two original polynomial-input cap halves. -/
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
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b c d : Under R} (f : a ⟶ b) (p : b ⟶ c) (q : c ⟶ d)
local notation "A" => CoefficientBassRaw1ChartCompositionProduct.polynomialInput P f
local notation "F" => CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q
local notation "J" => BassMWholeNerve.coefficientModel P (β.app d)
local notation "G" => CoefficientBassRaw1PolynomialPausedChart.sheetReference P β p q
local notation "ε" => CutOpenPrecomp.anchor A F J G (Iso.refl _)

/-- Literal inclusion into the existing two-sheet evaluator, with the same ordinary anchor. -/
def embed : C(carrier P β f p q, CutOpenCarrier.space (A ≫ F) J (A ≫ G) ε ε) :=
  (SSet.toTop.map (left₁ (A ≫ F) J (A ≫ G) ε ε)).hom

/-- Every input is evaluated at its own polynomial model, through the original first sheet. -/
def evaluate (n : ℕ) (z : carrier P β f p q) :=
  nativeEval (A ≫ F) J (A ≫ G) ε ε n (embed P β f p q z)

/-- Whole source-precomposition is exact on every point of the old first sheet. -/
theorem precomp_native (n : ℕ)
    (z : CoefficientBassRaw1PolynomialPairCone.carrier P β p q)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    evaluate P β f p q n (precomp P β f p q z) x =
      CoefficientBassRaw1PolynomialPairCone.evaluate P β p q n z
        ((prespectrumMap A).map n x) := by
  have h := CutOpenPrecomp.map_native A F J G (Iso.refl _) (Iso.refl _) n
    (CoefficientBassRaw1PolynomialPairCone.embed P β p q z) x
  have he := ConcreteCategory.congr_hom
    (CutOpenPrecomp.map_first A F J G (Iso.refl _) (Iso.refl _)) z
  change CutOpenPrecomp.map A F J G (Iso.refl _) (Iso.refl _)
      (CoefficientBassRaw1PolynomialPairCone.embed P β p q z) =
    embed P β f p q (precomp P β f p q z) at he
  rw [he] at h
  exact h

/-- The second half is exactly the old corrected pair cap on the polynomial coefficient image. -/
theorem last_native (n : ℕ) (r h : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    evaluate P β f p q n (last P β f p q (r, h)) x =
      CoefficientBassRaw1PolynomialPairCone.evaluate P β p q n
        (CoefficientBassRaw1PolynomialPairCone.corrected P β p q (r, h))
        ((prespectrumMap A).map n x) :=
  precomp_native P β f p q n _ x

/-- The first half is the original Laurent composition on the actual chart-square input. -/
theorem first_native (n : ℕ) (r t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    evaluate P β f p q n (first P β f p q (r, t)) x =
      (mappingConeInclusion (prespectrumMap J)).map n
        ((boundedFlatCoefficientLaurentCompositionHomotopy P p q).level n
          (r, (boundedFlatPerfectPrespectrumSquareHomotopy
            (coefficientMap P ((laurentUnderFunctor R).map f)) (coefficientMap P (β.app a))
            (coefficientMap P (β.app b))
            (coefficientMap P ((polynomialUnderFunctor R).map f))
            (coefficientMap_naturality P β f)).level n (t, x))) := by
  change nativeEval (A ≫ F) J (A ≫ G) ε ε n
    (laurentInclusion (A ≫ F) J (A ≫ G) ε ε
      (mapParameter (CommonReferenceProduct.reanchor
        (CoefficientBassRaw1ChartCompositionProduct.midpointIso P β f p q).symm)
        (CoefficientBassRaw1ChartCompositionProduct.family P β f p q (r, t)))) x = _
  rw [nativeEval_laurentInclusion, pointwise_reanchor,
    CoefficientBassRaw1ChartCompositionProduct.family_native]

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialInputCap
