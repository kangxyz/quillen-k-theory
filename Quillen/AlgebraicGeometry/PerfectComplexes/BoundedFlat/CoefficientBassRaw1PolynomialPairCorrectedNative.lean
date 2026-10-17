/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPairCorrected
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPairInitialNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConeCorrectedNative

/-! Exact original cone-composition caps on arbitrary genuine polynomial inputs. -/
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
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialPairCone
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The original native three-piece word is shared; no overlap-input recovery is used here. -/
abbrev nativeFirst := BassMWholeConeCarrier.nativeFirst P p q
/-- The unchanged second native cap from the original whole-cone composition carrier. -/
abbrev nativeSecond := BassMWholeConeCarrier.nativeSecond P p q
/-- The unchanged third native cap from the original whole-cone composition carrier. -/
abbrev nativeThird := BassMWholeConeCarrier.nativeThird P p q

private theorem corrected_of_initial
    (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (n : ℕ) (y : (HomotopyPushout.prespectrum
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).space n)
    (ev : carrier P β p q →
      (mappingCone (boundedFlatCoefficientBassSquareComparison P c)).space n)
    (hi : ∀ r s, ev (initial P β p q (r, s)) =
      (initialNative P p q).level n (r, (s, y))) (r s : I) :
    ev (corrected P β p q (r, s)) =
      (BassMWholeConeCarrier.nativeNullSquare P p q).level n (r, (s, y)) := by
  have hu (t : I) : ev (upperWord P β p q t) =
      (((nativeFirst P p q).trans (nativeSecond P p q)).trans
        (nativeThird P p q)).level n (t, y) := by
    rw [upperWord_apply]
    exact ((hi 1 t).trans ((initialNative P p q).at_one n t y)).trans
      (congrArg (fun f ↦ f (t, y)) (ConeCompositionPieces.source_level
        (boundedFlatCoefficientBassSquareComparison P c)
        (boundedFlatCoefficientPolynomialSpanMap P p)
        (boundedFlatCoefficientPolynomialSpanMap P q)
        (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map q)))
        (boundedFlatCoefficientBassComparisonHomotopy P p)
        (boundedFlatCoefficientBassComparisonHomotopy P q) n))
  have h12 (t : I) : ev (((firstPath P β p q).trans (secondPath P β p q)) t) =
      ((nativeFirst P p q).trans (nativeSecond P p q)).level n (t, y) :=
    NativeFactorEvaluation.left_factor n y ev
      ((firstPath P β p q).trans (secondPath P β p q)) (thirdPath P β p q)
      ((nativeFirst P p q).trans (nativeSecond P p q)) (nativeThird P p q) hu t
  have h1 (t : I) : ev (firstPath P β p q t) = (nativeFirst P p q).level n (t, y) :=
    NativeFactorEvaluation.left_factor n y ev (firstPath P β p q) (secondPath P β p q)
      (nativeFirst P p q) (nativeSecond P p q) h12 t
  have h2 (t : I) : ev (secondPath P β p q t) = (nativeSecond P p q).level n (t, y) :=
    NativeFactorEvaluation.right_factor n y ev (firstPath P β p q) (secondPath P β p q)
      (nativeFirst P p q) (nativeSecond P p q) h12 t
  have h3 (t : I) : ev (thirdPath P β p q t) = (nativeThird P p q).level n (t, y) :=
    NativeFactorEvaluation.right_factor n y ev
      ((firstPath P β p q).trans (secondPath P β p q)) (thirdPath P β p q)
      ((nativeFirst P p q).trans (nativeSecond P p q)) (nativeThird P p q) hu t
  have hj (r s : I) : ev (correction P β p q (r, s)) =
      (BassMWholeConeCarrier.nativeCorrection P p q).level n (r, (s, y)) := by
    have h := Path.Evaluation.transAssoc ev
      (firstPath P β p q) (secondPath P β p q) (thirdPath P β p q)
      ((nativeFirst P p q).path n y) ((nativeSecond P p q).path n y)
      ((nativeThird P p q).path n y) h1 h2 h3 r s
    exact h.trans (ConeCompositionPieces.correction_apply
      (boundedFlatCoefficientBassSquareComparison P c)
      (boundedFlatCoefficientPolynomialSpanMap P p)
      (boundedFlatCoefficientPolynomialSpanMap P q)
      (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map q)))
      (boundedFlatCoefficientBassComparisonHomotopy P p)
      (boundedFlatCoefficientBassComparisonHomotopy P q) n r s y).symm
  have hb (r s : I) : ev (correctedBoundary P β p q (r, s)) =
      (BassMWholeConeCarrier.nativeBoundary P p q).level n (r, (s, y)) :=
    CarrierPathSquare.correctedBoundary_native (initialSquare P β p q) (correction P β p q)
      (initialNative P p q) (BassMWholeConeCarrier.nativeCorrection P p q) n y ev hi hj r s
  have h := CarrierPathSquare.boundarySquare_native (correctedBoundary P β p q)
    (BassMWholeConeCarrier.nativeBoundary P p q) n y ev hb r s
  exact h.trans (congrArg (fun S ↦ S.level n (r, (s, y)))
    (BassMWholeConeCarrier.nativeBoundary_toSquare P p q))

/-- The selected old cone-composition cap, on every genuine plus polynomial input. -/
theorem plusValue_corrected (n : ℕ) (r h : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    plusValue P p q n (corrected P (underToLaurent R) p q (r, h)) x =
      (BassMWhole.coneComposition P p q).level n
        (r, ReducedMappingCone.cylinder _ _
          ((boundedFlatCoefficientBassSquareComparison P a).map n)
          (h, (HomotopyPushout.inl
            (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
            (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x)) :=
  corrected_of_initial P p q (underToLaurent R) n _
    (fun z ↦ plusValue P p q n z x)
    (fun r s ↦ plusValue_initial P p q n r s x) r h

/-- The selected old cone-composition cap, on every genuine minus polynomial input. -/
theorem minusValue_corrected (n : ℕ) (r h : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    minusValue P p q n (corrected P (underToLaurentInvert R) p q (r, h)) x =
      (BassMWhole.coneComposition P p q).level n
        (r, ReducedMappingCone.cylinder _ _
          ((boundedFlatCoefficientBassSquareComparison P a).map n)
          (h, (HomotopyPushout.inr
            (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
            (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x)) :=
  corrected_of_initial P p q (underToLaurentInvert R) n _
    (fun z ↦ minusValue P p q n z x)
    (fun r s ↦ minusValue_initial P p q n r s x) r h

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialPairCone
