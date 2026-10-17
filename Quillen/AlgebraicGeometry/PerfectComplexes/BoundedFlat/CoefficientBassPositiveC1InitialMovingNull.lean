/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Topology.Prespectrum.ConeSquareMovingNullEvaluation
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC0CarrierSeed
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1BoundaryLift
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCutOpenEvaluation

/-! Initial C1 moving-null carrier square; the original reassociation correction is separate. -/
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
namespace Quillen.PerfectComplexes.CoefficientBassPositiveC1InitialMovingNull
open CommonReferenceNerve CoefficientBassPositiveC1BoundaryLift
open CoefficientBassPositiveC0CarrierSeed
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The complete paused chart in the original two-tip carrier. -/
def first : C(I × I, Carrier P p q) :=
  ⟨fun z ↦ includeLaurent P p q (chartParameter P p q z), by fun_prop⟩

/-- The complete paused polynomial track crossed with the ordinary cone interval. -/
def last : C(I × I, Carrier P p q) :=
  ⟨fun z ↦ minusCylinder P p q (polynomialParameter P p q z.1, z.2), by fun_prop⟩

/-- The shared edge is the full reference-bearing chart attachment, at every time. -/
theorem seam (r : I) : first P p q (r, 1) = last P p q (r, 0) := by
  change includeLaurent P p q (chartParameter P p q (r, 1)) =
    minusCylinder P p q (polynomialParameter P p q r, 0)
  rw [chart_right_attach]
  exact (CutOpenCarrier.cylinderMinus_zero _ _ _ _ _ _).symm

/-- The entire initial Laurent edge before the original path-coordinate pasting. -/
def leftEdge : C(I, Carrier P p q) :=
  ⟨fun r ↦ first P p q (r, 0), by fun_prop⟩
/-- The shared full chart attachment edge, with its original reference. -/
def middleEdge : C(I, Carrier P p q) :=
  ⟨fun r ↦ first P p q (r, 1), by fun_prop⟩
/-- The final ordinary-cylinder edge, retaining the distinct ordinary tip. -/
def rightEdge : C(I, Carrier P p q) :=
  ⟨fun r ↦ last P p q (r, 1), by fun_prop⟩

/-- The full chart with coordinates exchanged for path-coordinate concatenation. -/
def firstSwap : (leftEdge P p q).Homotopy (middleEdge P p q) where
  toFun z := first P p q (z.2, z.1)
  continuous_toFun := by fun_prop
  map_zero_left _ := rfl
  map_one_left _ := rfl

/-- The full polynomial cylinder with the exact attachment seam as its source. -/
def lastSwap : (middleEdge P p q).Homotopy (rightEdge P p q) where
  toFun z := last P p q (z.2, z.1)
  continuous_toFun := by fun_prop
  map_zero_left r := (seam P p q r).symm
  map_one_left _ := rfl

/-- Paste in the original path coordinate, retaining exactly its two half clocks. -/
def parameter : C(I × I, Carrier P p q) :=
  ⟨fun z ↦ ((firstSwap P p q).trans (lastSwap P p q)) (z.2, z.1), by fun_prop⟩

/-- The first edge remains the complete Laurent chart edge. -/
theorem parameter_left (r : I) : parameter P p q (r, 0) = first P p q (r, 0) :=
  ((firstSwap P p q).trans (lastSwap P p q)).apply_zero r

/-- The terminal edge is the ordinary tip, without identifying the two carrier tips. -/
theorem parameter_right (r : I) : parameter P p q (r, 1) = minusTip P p q := by
  exact (((firstSwap P p q).trans (lastSwap P p q)).apply_one r).trans
    (CutOpenCarrier.cylinderMinus_one _ _ _ _ _ _)

/-- Precisely the initial moving square used before the original correction R. -/
abbrev initialNative := coneSquareNullMovingSquare
  (boundedFlatPerfectPrespectrumMap (laurentPlus P a))
  (boundedFlatPerfectPrespectrumMap (laurentPlus P c))
  (boundedFlatCoefficientPlusSquareHomotopy P (p ≫ q))
  (coneSquarePastedHomotopy
    (boundedFlatPerfectPrespectrumMap (laurentPlus P a))
    (boundedFlatPerfectPrespectrumMap (laurentPlus P b))
    (boundedFlatPerfectPrespectrumMap (laurentPlus P c))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map p)))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map p)))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map q)))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map q)))
    (boundedFlatCoefficientPlusSquareHomotopy P p)
    (boundedFlatCoefficientPlusSquareHomotopy P q))
  (CoefficientBassPositiveCompositionTrack.polynomialComposition P p q)
  (boundedFlatCoefficientLaurentCompositionHomotopy P p q)
  (CoefficientBassPositiveCompositionTrack.comparisonSquare P p q)

private theorem comparisonSquare_level (n : ℕ) :
    (CoefficientBassPositiveCompositionTrack.comparisonSquare P p q).level n =
      (boundedFlatCoefficientBassCompositionPlusChart P p q).level n := rfl

/-- This initial square retains every original native level and both independent square times. -/
theorem parameter_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CutOpenCarrier.nativeEval (polynomialReference P p q) (chartMap P (c := c))
      (laurentReference P p q) (ordinaryAnchor P p q)
      (LaurentUnitReferenceSpecialization.shiftedAnchor P p q) n (parameter P p q (r, s)) x =
    (initialNative P p q).level n
      (r, (s, (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)).map n x)) := by
  change CutOpenCarrier.nativeEval _ _ _ _ _ n
    (((firstSwap P p q).trans (lastSwap P p q)) (s, r)) x = _
  rw [ContinuousMap.Homotopy.trans_apply, initialNative, coneSquareNullMovingSquare_apply]
  split_ifs
  · change CutOpenCarrier.nativeEval _ _ _ _ _ n
      (includeLaurent P p q (chartParameter P p q (r, _))) x = _
    rw [CutOpenCarrier.nativeEval_laurentInclusion, pointwisePrespectrumFamily_eq_compact,
      comparisonSquare_level]
    exact congrArg ((mappingConeInclusion
      (boundedFlatPerfectPrespectrumMap (laurentPlus P c))).map n)
      (chartParameter_native P p q n r _ x)
  · change CutOpenCarrier.nativeEval _ _ _ _ _ n
      (minusCylinder P p q (polynomialParameter P p q r, _)) x = _
    rw [CutOpenCarrier.nativeEval_cylinderMinus, pointwisePrespectrumFamily_eq_compact]
    exact congrArg (fun y ↦ ReducedMappingCone.cylinder _ _
      ((boundedFlatPerfectPrespectrumMap (laurentPlus P c)).map n) (_, y))
      (polynomialParameter_native P p q n r x)

end Quillen.PerfectComplexes.CoefficientBassPositiveC1InitialMovingNull
