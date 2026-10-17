/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialInputEvaluation
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPostcompNative

/-! The two original polynomial caps share the literal normalized triple sheet. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
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

/-- The original right-first normalization identifies the actual source-precomposed pair. -/
def polynomialIso : (CoefficientBassRaw1PolynomialPostcomp.reference P f p q).functor ≅
    (A ≫ F).functor :=
  NormalizedTripleSimplex.rightFirst
    (coefficientMap P ((polynomialUnderFunctor R).map q))
    (coefficientMap P ((polynomialUnderFunctor R).map p))
    (coefficientMap P ((polynomialUnderFunctor R).map f))

/-- This literal first-sheet map puts the old cap in the same full triple as the other cap. -/
def place : C(carrier P β f p q,
    CoefficientBassRaw1PolynomialPostcomp.carrier P f p q β) :=
  CoefficientBassPolynomialSheetNormalization.map (A ≫ F)
    (CoefficientBassRaw1PolynomialPostcomp.reference P f p q) J (A ≫ G) ε
    (polynomialIso P f p q)

/-- The complete original outer-height surface is retained under this full reference change. -/
def placedFamily : C(I × I, CoefficientBassRaw1PolynomialPostcomp.carrier P f p q β) :=
  (place P β f p q).comp (family P β f p q)

/-- Actual first-sheet reference normalization preserves every native input and point. -/
theorem place_native (n : ℕ) (z : carrier P β f p q)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    CoefficientBassRaw1PolynomialPostcomp.evaluate P f p q β n (place P β f p q z) x =
      evaluate P β f p q n z x :=
  CoefficientBassPolynomialSheetNormalization.map_native (A ≫ F)
    (CoefficientBassRaw1PolynomialPostcomp.reference P f p q) J (A ≫ G) ε
    (polynomialIso P f p q) n z x

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialInputCap
