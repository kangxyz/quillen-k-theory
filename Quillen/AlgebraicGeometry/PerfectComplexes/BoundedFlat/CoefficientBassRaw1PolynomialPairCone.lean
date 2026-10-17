/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPausedChart
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCutOpenCompactFamily

/-! The original paused chart square in its literal first unreduced polynomial sheet. -/
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
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)
local notation "F" => CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q
local notation "J" => BassMWholeNerve.coefficientModel P (β.app c)
local notation "G" => CoefficientBassRaw1PolynomialPausedChart.sheetReference P β p q

/-- The pair's single sheet, without choosing a new filler. -/
abbrev scalar := firstSimplicial F J G (Iso.refl _)
/-- The realized first polynomial sheet of the original paused chart square. -/
abbrev carrier := |scalar P β p q|

/-- Literal inclusion of the first sheet into the existing evaluator's carrier. -/
def embed : C(carrier P β p q, CutOpenCarrier.space F J G (Iso.refl _) (Iso.refl _)) :=
  (SSet.toTop.map (left₁ F J G (Iso.refl _) (Iso.refl _))).hom

/-- The entire prescribed Q square lies in the Laurent summand before cone contraction. -/
def chartSquare : C(I × I, carrier P β p q) :=
  (SSet.toTop.map (left₀ F J G (Iso.refl _))).hom.comp
    (CoefficientBassRaw1PolynomialPausedChart.sheetFamily P β p q)

/-- The first-sheet evaluation is the existing all-degree evaluator restricted literally. -/
def evaluate (n : ℕ) (z : carrier P β p q) :=
  nativeEval F J G (Iso.refl _) (Iso.refl _) n (embed P β p q z)

/-- This recovers the exact original Q-postcomposition piece, with its terminal pause. -/
theorem chartSquare_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    evaluate P β p q n (chartSquare P β p q (r, s)) x =
      (mappingConeInclusion (prespectrumMap J)).map n
        (((CoefficientTransformationComposition.movingSquare P β p q).pauseRight).level n
          (r, (s, x))) := by
  change nativeEval F J G (Iso.refl _) (Iso.refl _) n
    (laurentInclusion F J G (Iso.refl _) (Iso.refl _)
      (CoefficientBassRaw1PolynomialPausedChart.sheetFamily P β p q (r, s))) x = _
  rw [nativeEval_laurentInclusion,
    CoefficientBassRaw1PolynomialPausedChart.sheetFamily_native]

/-- Joint continuity is inherited on every actual compact scalar family. -/
def compactFamily {S : Type u} [TopologicalSpace S] [CompactSpace S]
    (f : C(S, carrier P β p q)) (n : ℕ) :=
  compactNativeFamily F J G (Iso.refl _) (Iso.refl _) ((embed P β p q).comp f) n

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialPairCone
