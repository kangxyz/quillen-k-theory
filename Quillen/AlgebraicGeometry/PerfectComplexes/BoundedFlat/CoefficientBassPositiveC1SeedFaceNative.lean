/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Aglib.Topology.Path.HomotopyEvaluationTrans
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveSupportCompositionFactor
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1SeedFace
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1SourceProductNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1CorrectedNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1ShiftedCorrectedNative

/-! Exact native evaluation of the five-branch C1 face on the genuine original seed loop. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveC1SeedFaceNative
open CommonReferenceNerve CoefficientBassPositiveC1BoundaryLift
open CoefficientBassPositiveC0CarrierAttachment
open CoefficientBassPositiveC1SeedFace CoefficientBassPositiveC1SourceProductStrips
open CoefficientBassPositiveC1SourceProductNative CoefficientBassPositiveCompositionTrack
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The already constructed native evaluator of the common two-tip carrier. -/
abbrev evaluate (n : ℕ) := CutOpenCarrier.nativeEval
  (polynomialReference P p q) (chartMap P (c := c)) (laurentReference P p q)
  (ordinaryAnchor P p q) (LaurentUnitReferenceSpecialization.shiftedAnchor P p q) n
/-- The unchanged positive half of the original source null. -/
abbrev originalProjection := (boundedFlatCoefficientLaurentPlusHomotopy P a).postcomp
  (mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P a)))
/-- The unchanged original source cylinder, including the whole polynomial projection input. -/
abbrev originalContraction := Homotopy.precomp
  (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
  (mappingConeHomotopy (boundedFlatPerfectPrespectrumMap (laurentPlus P a)))
/-- The original forward source unit, before the actual cone composition is applied. -/
abbrev originalUnit := (boundedFlatCoefficientLaurentUnitHomotopy P a).postcomp
  (mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P a)))

/-- The actual cone composition on its Laurent inclusion keeps the original composition track. -/
theorem composition_inclusion (n : ℕ) (r : I)
    (y : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj a)))).space n) :
    (coneComposition P p q).level n
      (r, (mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P a))).map n y) =
    (mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P c))).map n
      ((boundedFlatCoefficientLaurentCompositionHomotopy P p q).level n (r, y)) := rfl

variable (n : ℕ) (r s : I)
  (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n)

/-- Ordinary positive native image, with the source track inside the cone composition. -/
theorem positiveMinus_native : evaluate P p q n (positiveMinus P p q (s, r)) x =
    (coneComposition P p q).level n (r, (originalProjection P (a := a)).level n (s, x)) := by
  refine (CutOpenCarrier.nativeEval_laurentInclusion
    (polynomialReference P p q) (chartMap P (c := c)) (laurentReference P p q)
    (ordinaryAnchor P p q) (LaurentUnitReferenceSpecialization.shiftedAnchor P p q)
    n (positiveParameter P p q (r, s)) x).trans ?_
  exact (congrArg
    ((mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P c))).map n)
    ((pointwisePrespectrumFamily_eq_compact (BassOverlap.commonReference P p q)
      (positiveParameter P p q) n (r, s) x).trans
      (positiveParameter_native P p q n r s x))).trans
    (composition_inclusion P p q n r
      ((boundedFlatCoefficientLaurentPlusHomotopy P a).level n (s, x))).symm

/-- The shifted positive native image retains its distinct full reference before evaluation. -/
theorem positivePlus_native : evaluate P p q n (positivePlus P p q (s, r)) x =
    (coneComposition P p q).level n (r, (originalProjection P (a := a)).level n (s, x)) := by
  refine (CutOpenCarrier.nativeEval_laurentInclusion
    (polynomialReference P p q) (chartMap P (c := c)) (laurentReference P p q)
    (ordinaryAnchor P p q) (LaurentUnitReferenceSpecialization.shiftedAnchor P p q)
    n (shiftedPositiveParameter P p q (r, s)) x).trans ?_
  exact (congrArg
    ((mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P c))).map n)
    ((pointwisePrespectrumFamily_eq_compact (BassOverlap.commonReference P p q)
      (shiftedPositiveParameter P p q) n (r, s) x).trans
      (shiftedPositiveParameter_native P p q n r s x))).trans
    (composition_inclusion P p q n r
      ((boundedFlatCoefficientLaurentPlusHomotopy P a).level n (s, x))).symm

/-- Ordinary corrected-square evaluation is the cone composition on the original source cylinder. -/
theorem correctedMinus_native : evaluate P p q n (correctedMinus P p q (s, r)) x =
    (coneComposition P p q).level n (r, (originalContraction P (a := a)).level n (s, x)) :=
  (CoefficientBassPositiveC1CorrectedNative.correctedSquare_native P p q n r s x).trans
    (coneComposition_cylinder P p q n r s
      ((boundedFlatPerfectPrespectrumMap (polynomialProjection P a)).map n x)).symm

/-- The shifted corrected square has the same native image through its own plus cylinder. -/
theorem correctedPlus_native : evaluate P p q n (correctedPlus P p q (s, r)) x =
    (coneComposition P p q).level n (r, (originalContraction P (a := a)).level n (s, x)) :=
  (CoefficientBassPositiveC1ShiftedCorrectedNative.correctedSquare_native P p q n r s x).trans
    (coneComposition_cylinder P p q n r s
      ((boundedFlatPerfectPrespectrumMap (polynomialProjection P a)).map n x)).symm

/-- The forward unit is evaluated on the genuine source input, before cone composition. -/
theorem forwardUnit_native : evaluate P p q n (forwardUnit P p q (s, r)) x =
    (coneComposition P p q).level n (r, (originalUnit P (a := a)).level n (s, x)) := by
  refine (CutOpenCarrier.nativeEval_laurentInclusion
    (polynomialReference P p q) (chartMap P (c := c)) (laurentReference P p q)
    (ordinaryAnchor P p q) (LaurentUnitReferenceSpecialization.shiftedAnchor P p q)
    n (unitParameter P p q (r, s)) x).trans ?_
  exact (congrArg
    ((mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P c))).map n)
    ((pointwisePrespectrumFamily_eq_compact (BassOverlap.commonReference P p q)
      (unitParameter P p q) n (r, s) x).trans
      (unitParameter_native P p q n r s x))).trans
    (composition_inclusion P p q n r
      ((boundedFlatCoefficientLaurentUnitHomotopy P a).level n (s, x))).symm

/-- Both original halves of the ordinary null are preserved under the fixed-time cone map. -/
theorem nullMinus_native : evaluate P p q n (nullMinus P p q (s, r)) x =
    (coneComposition P p q).level n
      (r, (boundedFlatCoefficientBassPositiveConeNull P a).level n (s, x)) :=
  ContinuousMap.Homotopy.Evaluation.trans_compare (positiveMinus P p q) (correctedMinus P p q)
    ((originalProjection P (a := a)).levelHomotopy n).toHomotopy
    ((originalContraction P (a := a)).levelHomotopy n).toHomotopy
    (fun y ↦ evaluate P p q n y x) (fun y ↦ (coneComposition P p q).level n (r, y)) r x
    (fun t ↦ positiveMinus_native P p q n r t x)
    (fun t ↦ correctedMinus_native P p q n r t x) s

/-- The shifted null preserves the same original halves while retaining a separate carrier tip. -/
theorem nullPlus_native : evaluate P p q n (nullPlus P p q (s, r)) x =
    (coneComposition P p q).level n
      (r, (boundedFlatCoefficientBassPositiveConeNull P a).level n (s, x)) :=
  ContinuousMap.Homotopy.Evaluation.trans_compare (positivePlus P p q) (correctedPlus P p q)
    ((originalProjection P (a := a)).levelHomotopy n).toHomotopy
    ((originalContraction P (a := a)).levelHomotopy n).toHomotopy
    (fun y ↦ evaluate P p q n y x) (fun y ↦ (coneComposition P p q).level n (r, y)) r x
    (fun t ↦ positivePlus_native P p q n r t x)
    (fun t ↦ correctedPlus_native P p q n r t x) s

/-- Exact fixed C1 on the genuine original seed loop, at every level and independent time. -/
theorem face_native : evaluate P p q n (face P p q (r, s)) x =
    Path.toContinuousMap ((CoefficientBassPositiveCompositionTrack.stepComposition P p q).level n
      (r, (boundedFlatCoefficientBassPositiveConeSeed P a).map n x)) s := by
  let N := boundedFlatCoefficientBassPositiveConeNull P a
  let U := originalUnit P (a := a)
  change evaluate P p q n
    (((nullMinus P p q).symm.trans ((forwardUnit P p q).trans (nullPlus P p q))) (s, r)) x =
    (coneComposition P p q).level n (r, (N.symm.trans (U.trans N)).level n (s, x))
  refine ContinuousMap.Homotopy.Evaluation.trans_compare (nullMinus P p q).symm
    ((forwardUnit P p q).trans (nullPlus P p q))
    ((N.symm).levelHomotopy n).toHomotopy ((U.trans N).levelHomotopy n).toHomotopy
    (fun y ↦ evaluate P p q n y x) (fun y ↦ (coneComposition P p q).level n (r, y)) r x
    (fun t ↦ nullMinus_native P p q n r (unitInterval.symm t) x) ?_ s
  intro t
  exact ContinuousMap.Homotopy.Evaluation.trans_compare (forwardUnit P p q) (nullPlus P p q)
    (U.levelHomotopy n).toHomotopy (N.levelHomotopy n).toHomotopy
    (fun y ↦ evaluate P p q n y x) (fun y ↦ (coneComposition P p q).level n (r, y)) r x
    (fun v ↦ forwardUnit_native P p q n r v x)
    (fun v ↦ nullPlus_native P p q n r v x) t

/-- Only after evaluation does the minus endpoint become the native basepoint. -/
theorem face_bottom_native : evaluate P p q n (face P p q (r, 0)) x =
    (CutOpenCarrier.nativeCone (chartMap P (c := c))).point n := by
  rw [face_bottom]
  exact CutOpenCarrier.nativeEval_tipMinus _ _ _ _ _ n x

/-- The separate plus endpoint has the same native basepoint image. -/
theorem face_top_native : evaluate P p q n (face P p q (r, 1)) x =
    (CutOpenCarrier.nativeCone (chartMap P (c := c))).point n := by
  rw [face_top]
  exact CutOpenCarrier.nativeEval_tipPlus _ _ _ _ _ n x

end Quillen.PerfectComplexes.CoefficientBassPositiveC1SeedFaceNative
