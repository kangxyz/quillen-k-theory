/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC0PolynomialEndpoints
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC0TenNodes

/-!
# Literal original C0 null and seed paths in the two-tip carrier

The two nulls use their original halves. Their literal null-minus inverse, forward unit,
and null-plus word defines a jointly continuous face. No reassociation, replacement speed,
tip identification, or higher filler is used. Native recovery is a separate upper owner.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveC0CarrierSeed
open CommonReferenceNerve CoefficientBassPositiveC1BoundaryLift
open CoefficientBassPositiveC0CarrierAttachment CoefficientBassPositiveC0CarrierRails
open CoefficientBassPositiveC0UnitStrip CoefficientBassPositiveC0PolynomialEndpoints
open CoefficientBassPositiveC0TenNodes
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The two-tip carrier with the ordinary and forward-unit shifted polynomial attachments. -/
abbrev Carrier := CutOpenCarrier.space (polynomialReference P p q) (chartMap P (c := c))
  (laurentReference P p q) (ordinaryAnchor P p q)
  (LaurentUnitReferenceSpecialization.shiftedAnchor P p q)
/-- The continuous inclusion of the Laurent reference into the two-tip carrier. -/
abbrev includeLaurent := CutOpenCarrier.laurentInclusion
  (polynomialReference P p q) (chartMap P (c := c)) (laurentReference P p q)
  (ordinaryAnchor P p q) (LaurentUnitReferenceSpecialization.shiftedAnchor P p q)
/-- The ordinary polynomial cylinder, from its Laurent attachment at time zero to its tip at
time one. -/
abbrev minusCylinder := CutOpenCarrier.cylinderMinus
  (polynomialReference P p q) (chartMap P (c := c)) (laurentReference P p q)
  (ordinaryAnchor P p q) (LaurentUnitReferenceSpecialization.shiftedAnchor P p q)
/-- The shifted polynomial cylinder, from its Laurent attachment at time zero to its tip at time
one. -/
abbrev plusCylinder := CutOpenCarrier.cylinderPlus
  (polynomialReference P p q) (chartMap P (c := c)) (laurentReference P p q)
  (ordinaryAnchor P p q) (LaurentUnitReferenceSpecialization.shiftedAnchor P p q)
/-- The terminal point of the ordinary polynomial cylinder. -/
abbrev minusTip := CutOpenCarrier.tipMinus
  (polynomialReference P p q) (chartMap P (c := c)) (laurentReference P p q)
  (ordinaryAnchor P p q) (LaurentUnitReferenceSpecialization.shiftedAnchor P p q)
/-- The terminal point of the shifted polynomial cylinder. -/
abbrev plusTip := CutOpenCarrier.tipPlus
  (polynomialReference P p q) (chartMap P (c := c)) (laurentReference P p q)
  (ordinaryAnchor P p q) (LaurentUnitReferenceSpecialization.shiftedAnchor P p q)

/-- The ordinary projection at seed time zero, parameterized by coefficient time. -/
def ordinaryStart : C(I, Carrier P p q) :=
  ⟨fun r ↦ includeLaurent P p q (positiveProjectionParameter P p q (r, 0)), by fun_prop⟩
/-- The ordinary projection at seed time one, parameterized by coefficient time. -/
def ordinaryEnd : C(I, Carrier P p q) :=
  ⟨fun r ↦ includeLaurent P p q (positiveProjectionParameter P p q (r, 1)), by fun_prop⟩
/-- The shifted projection at seed time zero, parameterized by coefficient time. -/
def shiftedStart : C(I, Carrier P p q) :=
  ⟨fun r ↦ includeLaurent P p q (shiftedProjectionParameter P p q (r, 0)), by fun_prop⟩
/-- The shifted projection at seed time one, parameterized by coefficient time. -/
def shiftedEnd : C(I, Carrier P p q) :=
  ⟨fun r ↦ includeLaurent P p q (shiftedProjectionParameter P p q (r, 1)), by fun_prop⟩

/-- Original projection half, with seed time first and coefficient time second. -/
def projectionMinus : (ordinaryStart P p q).Homotopy (ordinaryEnd P p q) where
  toFun z := includeLaurent P p q (positiveProjectionParameter P p q (z.2, z.1))
  continuous_toFun := by fun_prop
  map_zero_left _ := rfl
  map_one_left _ := rfl

/-- The shifted projection half retains the actual commonUnit attachment. -/
def projectionPlus : (shiftedStart P p q).Homotopy (shiftedEnd P p q) where
  toFun z := includeLaurent P p q (shiftedProjectionParameter P p q (z.2, z.1))
  continuous_toFun := by fun_prop
  map_zero_left _ := rfl
  map_one_left _ := rfl

/-- Original polynomial contraction to the minus tip, using the whole accepted seam. -/
def contractionMinus : (ordinaryEnd P p q).Homotopy (ContinuousMap.const I (minusTip P p q)) where
  toFun z := minusCylinder P p q (coefficientPolynomialParameter P p q z.2, z.1)
  continuous_toFun := by fun_prop
  map_zero_left r := (ordinary_cutOpen_seam P p q r).symm
  map_one_left r := CutOpenCarrier.cylinderMinus_one _ _ _ _ _ _

/-- Separate polynomial contraction to the plus tip; the two tips are not identified. -/
def contractionPlus : (shiftedEnd P p q).Homotopy (ContinuousMap.const I (plusTip P p q)) where
  toFun z := plusCylinder P p q (coefficientPolynomialParameter P p q z.2, z.1)
  continuous_toFun := by fun_prop
  map_zero_left r := (shifted_cutOpen_seam P p q r).symm
  map_one_left r := CutOpenCarrier.cylinderPlus_one _ _ _ _ _ _

/-- Literal ordinary null with its original half-time cut. -/
def nullMinus := (projectionMinus P p q).trans (contractionMinus P p q)
/-- Literal shifted null with the same original half-time cut and its own tip. -/
def nullPlus := (projectionPlus P p q).trans (contractionPlus P p q)

/-- Forward unit strip at unchanged unit time; both endpoint joins are whole parameter equations. -/
def forwardUnit : (ordinaryStart P p q).Homotopy (shiftedStart P p q) where
  toFun z := includeLaurent P p q (unitProductParameter P p q (z.2, z.1))
  continuous_toFun := by fun_prop
  map_zero_left r := congrArg (includeLaurent P p q) (unitProduct_lower P p q r)
  map_one_left r := congrArg (includeLaurent P p q) (unitProduct_upper P p q r)

/-- The original parenthesized word gives precisely cuts 0,1/4,1/2,3/4,7/8,1. -/
def seedWord : (ContinuousMap.const I (minusTip P p q)).Homotopy
    (ContinuousMap.const I (plusTip P p q)) :=
  (nullMinus P p q).symm.trans ((forwardUnit P p q).trans (nullPlus P p q))

/-- Actual jointly continuous C0 face map, coefficient time first and original seed time second. -/
def face : C(I × I, Carrier P p q) :=
  ⟨fun z ↦ seedWord P p q (z.2, z.1), by fun_prop⟩

/-- Exact whole boundary word, without reassociation or changing either independent time. -/
theorem face_word (r s : I) : face P p q (r, s) =
    ((nullMinus P p q).symm.trans ((forwardUnit P p q).trans (nullPlus P p q))) (s, r) := rfl

theorem face_bottom (r : I) : face P p q (r, 0) = minusTip P p q :=
  (seedWord P p q).apply_zero r

theorem face_top (r : I) : face P p q (r, 1) = plusTip P p q :=
  (seedWord P p q).apply_one r

/-- Whole source ordinary projection rail, in its original full reference. -/
theorem source_projection (s : I) : projectionMinus P p q (s, 0) =
    includeLaurent P p q (sourceProjectionParameter P p q s) :=
  congrArg (includeLaurent P p q) (projection_source_rail P p q s)

/-- Whole target ordinary projection rail, after the original q-pre-p transport. -/
theorem target_projection (s : I) : projectionMinus P p q (s, 1) =
    includeLaurent P p q (targetProjectionParameter P p q s) :=
  congrArg (includeLaurent P p q) (projection_target_rail P p q s)

/-- Both whole source contraction rails retain the direct-composite polynomial input. -/
theorem source_contractions (s : I) :
    contractionMinus P p q (s, 0) = minusCylinder P p q (nodePoint _ (sourceNullNode P p q), s) ∧
    contractionPlus P p q (s, 0) = plusCylinder P p q (nodePoint _ (sourceNullNode P p q), s) :=
  source_cylinders P p q s

/-- Both whole target contraction rails retain the q-pre-p polynomial input. -/
theorem target_contractions (s : I) :
    contractionMinus P p q (s, 1) = minusCylinder P p q (nodePoint _ (targetNullNode P p q), s) ∧
    contractionPlus P p q (s, 1) = plusCylinder P p q (nodePoint _ (targetNullNode P p q), s) :=
  target_cylinders P p q s

/-- The whole source unit rail is the exact direct-composite TenNodes W edge. -/
theorem source_unit (t : I) : forwardUnit P p q (t, 0) = includeLaurent P p q
    (mapParameter (BassH0Merge.anchorNode (eqToIso (BassH0Merge.reference_eq P p q)))
      (parameter (CoefficientLaurentUnitTenNodes.source P (p ≫ q))
        (CoefficientLaurentUnitTenNodes.nodes P (p ≫ q)) (CoefficientLaurentUnitTenNodes.W t))) :=
  congrArg (includeLaurent P p q) (source_rail P p q t)

/-- The whole target unit rail is the original q TenNodes W edge precomposed by p. -/
theorem target_unit (t : I) : forwardUnit P p q (t, 1) = includeLaurent P p q
    (mapParameter (BassH0Merge.preReferenceNode (laurentReference P p q)
      (BassH1Components.coefficientMapModel P p) (BassH1References.middleIso P p q))
      (parameter (CoefficientLaurentUnitTenNodes.source P q)
        (CoefficientLaurentUnitTenNodes.nodes P q) (CoefficientLaurentUnitTenNodes.W t))) :=
  congrArg (includeLaurent P p q) (target_rail P p q t)

/-- Actual supportedRight C0 reverses only coefficient time, exactly once. -/
def reversedFace : C(I × I, Carrier P p q) :=
  ⟨fun z ↦ face P p q (unitInterval.symm z.1, z.2), by fun_prop⟩

theorem reversedFace_source (s : I) : reversedFace P p q (0, s) = face P p q (1, s) := by
  change face P p q (unitInterval.symm 0, s) = _
  simp

theorem reversedFace_target (s : I) : reversedFace P p q (1, s) = face P p q (0, s) := by
  change face P p q (unitInterval.symm 1, s) = _
  simp

/-- Shifted source projection rail with the actual common-unit reanchoring intact. -/
theorem source_projection_shifted (s : I) : projectionPlus P p q (s, 0) =
    includeLaurent P p q
      (mapParameter (BassH0Merge.anchorNode
        (LaurentUnitReferenceSpecialization.commonUnit P p q))
        (sourceProjectionParameter P p q s)) := by
  change includeLaurent P p q
    (mapParameter _ (positiveProjectionParameter P p q (0, s))) = _
  rw [projection_source_rail]

/-- Shifted target projection rail uses the same precise q-pre-p reanchoring. -/
theorem target_projection_shifted (s : I) : projectionPlus P p q (s, 1) =
    includeLaurent P p q
      (mapParameter (BassH0Merge.anchorNode
        (LaurentUnitReferenceSpecialization.commonUnit P p q))
        (targetProjectionParameter P p q s)) := by
  change includeLaurent P p q
    (mapParameter _ (positiveProjectionParameter P p q (1, s))) = _
  rw [projection_target_rail]

/-- At the actual source the direct-l W edge keeps polynomialUnderCoefficient_toLaurent. -/
theorem actual_source_unit (d : Under R) (t : I) :
    forwardUnit P ((polynomialUnderCoefficient R).app d) ((underToLaurent R).app d) (t, 0) =
    includeLaurent P ((polynomialUnderCoefficient R).app d) ((underToLaurent R).app d)
      (mapParameter (BassH0Merge.anchorNode (eqToIso (actualSourceReferenceEq P d)))
        (parameter (CoefficientLaurentUnitTenNodes.source P ((laurentUnderCoefficient R).app d))
          (CoefficientLaurentUnitTenNodes.nodes P ((laurentUnderCoefficient R).app d))
          (CoefficientLaurentUnitTenNodes.W t))) :=
  congrArg (includeLaurent P ((polynomialUnderCoefficient R).app d) ((underToLaurent R).app d))
    (actual_source_rail P d t)

/-- Original source boundary word at every seed time; its five full rails are identified above. -/
theorem face_source_word (s : I) : face P p q (0, s) =
    (((projectionMinus P p q).trans (contractionMinus P p q)).symm.trans
      ((forwardUnit P p q).trans
        ((projectionPlus P p q).trans (contractionPlus P p q)))) (s, 0) := rfl

/-- Original q-pre-p target boundary word with the same nested trans and all original cuts. -/
theorem face_target_word (s : I) : face P p q (1, s) =
    (((projectionMinus P p q).trans (contractionMinus P p q)).symm.trans
      ((forwardUnit P p q).trans
        ((projectionPlus P p q).trans (contractionPlus P p q)))) (s, 1) := rfl

end Quillen.PerfectComplexes.CoefficientBassPositiveC0CarrierSeed
