/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Aglib.Topology.Path.CarrierHalfPaths
public import Quillen.Topology.Prespectrum.ConeCompositionPieces
public import Quillen.Topology.Prespectrum.RelativeHomotopyFactorEvaluation
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1InitialMovingNull

/-! Whole carrier pieces and exact source join for the original C1 reassociation correction. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveC1ReassociationPieces
open CommonReferenceNerve CoefficientBassPositiveC1BoundaryLift
open CoefficientBassPositiveC0CarrierSeed
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The entire composite-side chart edge in the unchanged carrier. -/
def chartTop : C(I, Carrier P p q) :=
  ⟨fun s ↦ CoefficientBassPositiveC1InitialMovingNull.first P p q (1, s), by fun_prop⟩

/-- First literal half of the composite-side chart; no endpoint is replaced. -/
def firstPath := Path.CarrierHalfPaths.first (chartTop P p q)

/-- Second literal half, with the same actual midpoint. -/
def secondPath := Path.CarrierHalfPaths.last (chartTop P p q)

/-- The final polynomial cylinder begins at the full attached chart endpoint. -/
def thirdPath : Path (chartTop P p q 1) (minusTip P p q) where
  toFun s := CoefficientBassPositiveC1InitialMovingNull.last P p q (1, s)
  continuous_toFun := by fun_prop
  source' := (CoefficientBassPositiveC1InitialMovingNull.seam P p q 1).symm
  target' := CutOpenCarrier.cylinderMinus_one _ _ _ _ _ _

/-- The exact source parentheses and half/quarter clocks of the correction. -/
def upperWord := ((firstPath P p q).trans (secondPath P p q)).trans (thirdPath P p q)

/-- The whole initial upper edge, not only its native image, is the three-piece source word. -/
theorem upperWord_apply (s : I) : upperWord P p q s =
    CoefficientBassPositiveC1InitialMovingNull.parameter P p q (1, s) := by
  change (((firstPath P p q).trans (secondPath P p q)).trans (thirdPath P p q)) s =
    ((CoefficientBassPositiveC1InitialMovingNull.firstSwap P p q).trans
      (CoefficientBassPositiveC1InitialMovingNull.lastSwap P p q)) (s, 1)
  rw [Path.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact Path.CarrierHalfPaths.trans_apply (chartTop P p q) _
  · rfl

/-- The first literal native piece of the original correction R. -/
abbrev nativeFirst := ConeCompositionPieces.first
  (boundedFlatPerfectPrespectrumMap (laurentPlus P c))
  (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map p)))
  (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map q)))
  (boundedFlatCoefficientPlusSquareHomotopy P p)

/-- The second original piece, retaining its exact endpoint associativity casts. -/
abbrev nativeSecond := ConeCompositionPieces.second
  (boundedFlatPerfectPrespectrumMap (laurentPlus P c))
  (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map p)))
  (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map q)))
  (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map q)))
  (boundedFlatCoefficientPlusSquareHomotopy P q)

/-- The unchanged final native polynomial cylinder. -/
abbrev nativeThird := ConeCompositionPieces.third
  (boundedFlatPerfectPrespectrumMap (laurentPlus P c))
  (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map p)))
  (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map q)))

/-- The original projected source input; no loop coordinate is erased. -/
abbrev input (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :=
  (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)).map n x

/-- Pointwise native evaluation on the original two-tip carrier. -/
abbrev evaluate (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :=
  fun y ↦ CutOpenCarrier.nativeEval (polynomialReference P p q) (chartMap P (c := c))
    (laurentReference P p q) (ordinaryAnchor P p q)
    (LaurentUnitReferenceSpecialization.shiftedAnchor P p q) n y x

/-- The whole initial edge has the exact native source parentheses used by R.ofLevels. -/
theorem upperWord_native (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    evaluate P p q n x (upperWord P p q s) =
    (((nativeFirst P p q).trans (nativeSecond P p q)).trans (nativeThird P p q)).level n
      (s, input P n x) := by
  rw [upperWord_apply]
  have h := (CoefficientBassPositiveC1InitialMovingNull.parameter_native P p q n 1 s x).trans
    ((CoefficientBassPositiveC1InitialMovingNull.initialNative P p q).at_one n s (input P n x))
  exact h.trans (congrArg (fun f ↦ f (s, input P n x))
    (ConeCompositionPieces.source_level
      (boundedFlatPerfectPrespectrumMap (laurentPlus P c))
      (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map p)))
      (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map q)))
      (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map q)))
      (boundedFlatCoefficientPlusSquareHomotopy P p)
      (boundedFlatCoefficientPlusSquareHomotopy P q) n))

private theorem firstTwo_native (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    evaluate P p q n x (((firstPath P p q).trans (secondPath P p q)) s) =
      ((nativeFirst P p q).trans (nativeSecond P p q)).level n (s, input P n x) :=
  NativeFactorEvaluation.left_factor n (input P n x) (evaluate P p q n x)
    ((firstPath P p q).trans (secondPath P p q)) (thirdPath P p q)
    ((nativeFirst P p q).trans (nativeSecond P p q)) (nativeThird P p q)
    (fun t ↦ upperWord_native P p q n t x) s

/-- Full first-piece evaluation follows from the whole source word, including its midpoint. -/
theorem firstPath_native (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    evaluate P p q n x (firstPath P p q s) =
      (nativeFirst P p q).level n (s, input P n x) :=
  NativeFactorEvaluation.left_factor n (input P n x) (evaluate P p q n x)
    (firstPath P p q) (secondPath P p q) (nativeFirst P p q) (nativeSecond P p q)
    (fun t ↦ firstTwo_native P p q n t x) s

/-- Full second-piece evaluation retains the native original associativity endpoint casts. -/
theorem secondPath_native (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    evaluate P p q n x (secondPath P p q s) =
      (nativeSecond P p q).level n (s, input P n x) :=
  NativeFactorEvaluation.right_factor n (input P n x) (evaluate P p q n x)
    (firstPath P p q) (secondPath P p q) (nativeFirst P p q) (nativeSecond P p q)
    (fun t ↦ firstTwo_native P p q n t x) s

/-- Full final-cylinder evaluation, without deleting its original time coordinate. -/
theorem thirdPath_native (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    evaluate P p q n x (thirdPath P p q s) =
      (nativeThird P p q).level n (s, input P n x) :=
  NativeFactorEvaluation.right_factor n (input P n x) (evaluate P p q n x)
    ((firstPath P p q).trans (secondPath P p q)) (thirdPath P p q)
    ((nativeFirst P p q).trans (nativeSecond P p q)) (nativeThird P p q)
    (fun t ↦ upperWord_native P p q n t x) s

end Quillen.PerfectComplexes.CoefficientBassPositiveC1ReassociationPieces
