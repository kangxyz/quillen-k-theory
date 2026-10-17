/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeJ0Rectangles
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassH0Native
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveReanchorFamily
public import Quillen.Topology.Prespectrum.RelativeHomotopyEndpointEvaluation

/-!
# Exact native positive-pasting images of both actual carrier rectangles

The complete 31-node family is reanchored before its original rectangle is evaluated. The
actual p;q=l equality is retained. Neither positive binary rail is replaced by a TenNodes rail.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassCompositeJ0RectangleNative
open CommonReferenceNerve BassH0Merge CoefficientBassCompositeJ0ConeBoundaries
open CoefficientBassCompositeJ0Rectangles
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

private theorem ordinary_family_of_eq {a b c : Under R}
    (p : a ⟶ b) (q : b ⟶ c) (w : a ⟶ c) (hw : p ≫ q = w)
    (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    prespectrumFamily (BassOverlap.commonReference P p q) (BassH0Merge.nodes P p q) n
      (ProjectionRectangleParameters.rectangle BassH0Diagram.plusFace (r, s), x) =
    (boundedFlatCoefficientPlusPasting P w).level n (r, (s, x)) := by
  subst w
  rw [prespectrumFamily_eq]
  change prespectrumSimplexFamily (BassH0Merge.simplex P p q) n
    (ProjectionRectangleParameters.rectangle BassH0Diagram.plusFace (r, s), x) = _
  rw [BassH0Merge.simplex_original]
  exact BassH0Diagram.plus_rectangle_lift P (p ≫ q) n r s x

/-- The complete common-reference family gives the original positive rectangle at all levels. -/
theorem ordinary_family (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    prespectrumFamily (laurentRef P p q)
      (BassH0Merge.nodes P p q) n
      (ProjectionRectangleParameters.rectangle BassH0Diagram.plusFace (r, s), x) =
    (boundedFlatCoefficientPlusPasting P (arrow p q)).level n (r, (s, x)) := by
  exact ordinary_family_of_eq P p q (arrow p q)
    rfl n r s x

/-- The forward commonUnit changes full references, while preserving the entire native family. -/
theorem shifted_family (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    prespectrumFamily (laurentRef P p q)
      (fun i ↦ anchorNode
        (LaurentUnitReferenceSpecialization.commonUnit P p q)
        (BassH0Merge.nodes P p q i)) n
      (ProjectionRectangleParameters.rectangle BassH0Diagram.plusFace (r, s), x) =
    (boundedFlatCoefficientPlusPasting P (arrow p q)).level n (r, (s, x)) := by
  change prespectrumFamily (laurentRef P p q)
    (ModelSimplex.reanchorNodes
      (LaurentUnitReferenceSpecialization.commonUnit P p q)
      (BassH0Merge.nodes P p q)) n _ = _
  rw [prespectrumFamily_reanchor]
  exact ordinary_family P p q n r s x

/-- The whole minus rectangle evaluates to the original cone-postcomposed positive pasting. -/
theorem rectangleMinus_original_value (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n (rectangleMinus P p q (r, s)) x =
    (LoopPrespectrum.mappingConeInclusion (prespectrumMap (chart P (c := c)))).map n
      ((boundedFlatCoefficientPlusPasting P (arrow p q)).level n (r, (s, x))) := by
  rw [rectangleMinus_native_parameter, ordinary_family]

/-- The literal positivePasting type transport retains this entire native rectangle. -/
theorem rectangleMinus_positivePasting (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n (rectangleMinus P p q (r, s)) x =
    (CoefficientBassPositiveNullTrack.positivePasting P (arrow p q)).level n (r, (s, x)) := by
  rw [rectangleMinus_original_value]
  unfold CoefficientBassPositiveNullTrack.positivePasting
  symm
  apply LoopPrespectrum.Homotopy.RelHomotopy.transport_apply
  all_goals simp only [boundedFlatCoefficientPlusLeftTrack, boundedFlatCoefficientPlusRightTrack,
    LoopPrespectrum.Homotopy.postcomp_trans, LoopPrespectrum.Homotopy.postcomp_symm,
    CoefficientBassPositiveNullTrack.positiveMovement,
    CoefficientBassPositiveNullTrack.polynomialMovement,
    CoefficientBassPositiveNullTrack.oldPositive, CoefficientBassPositiveNullTrack.laurentMovement,
    CoefficientBassPositiveNullTrack.newPositive]

/-- The whole plus rectangle evaluates to the original cone-postcomposed positive pasting. -/
theorem rectanglePlus_original_value (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n (rectanglePlus P p q (r, s)) x =
    (LoopPrespectrum.mappingConeInclusion (prespectrumMap (chart P (c := c)))).map n
      ((boundedFlatCoefficientPlusPasting P (arrow p q)).level n (r, (s, x))) := by
  rw [rectanglePlus_native_parameter, shifted_family]

/-- The literal positivePasting type transport retains this entire native rectangle. -/
theorem rectanglePlus_positivePasting (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n (rectanglePlus P p q (r, s)) x =
    (CoefficientBassPositiveNullTrack.positivePasting P (arrow p q)).level n (r, (s, x)) := by
  rw [rectanglePlus_original_value]
  unfold CoefficientBassPositiveNullTrack.positivePasting
  symm
  apply LoopPrespectrum.Homotopy.RelHomotopy.transport_apply
  all_goals simp only [boundedFlatCoefficientPlusLeftTrack, boundedFlatCoefficientPlusRightTrack,
    LoopPrespectrum.Homotopy.postcomp_trans, LoopPrespectrum.Homotopy.postcomp_symm,
    CoefficientBassPositiveNullTrack.positiveMovement,
    CoefficientBassPositiveNullTrack.polynomialMovement,
    CoefficientBassPositiveNullTrack.oldPositive, CoefficientBassPositiveNullTrack.laurentMovement,
    CoefficientBassPositiveNullTrack.newPositive]

end Quillen.PerfectComplexes.CoefficientBassCompositeJ0RectangleNative
