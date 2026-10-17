/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveJ0ConeBoundaries
public import Quillen.Aglib.Topology.Path.MappedProjectionRectangle
/-!
# Both actual positive rectangles in the two-tip carrier

The original full-node 31-simplex and its commonUnit-shifted copy carry the unchanged positive
rectangle. Whole boundary words and polynomial/cone attachment seams are literal. No whole J0
comparison is assumed; identifying the remaining positive and unit rails is separate.
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
namespace Quillen.PerfectComplexes.CoefficientBassPositiveJ0Rectangles
open CommonReferenceNerve BassH0Merge CoefficientBassPositiveJ0ConeBoundaries
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (d : Under R)

/-- The unchanged two-tip carrier with both specified attachment references. -/
abbrev Carrier := CutOpenCarrier.space (polyRef P d) (chart P d) (laurentRef P d)
  (ordinary P d) (shifted P d)

/-- The entire ordinary full-node Laurent simplex, included in the actual carrier. -/
def ordinaryMap : C(StdSimplex ℝ (Fin 31), Carrier P d) :=
  (CutOpenCarrier.laurentInclusion (polyRef P d) (chart P d) (laurentRef P d)
    (ordinary P d) (shifted P d)).comp
    (parameter (laurentRef P d) (BassH0Merge.nodes P (firstArrow d) (secondArrow d)))

/-- The entire shifted full-node simplex uses the original commonUnit action. -/
def shiftedMap : C(StdSimplex ℝ (Fin 31), Carrier P d) :=
  (CutOpenCarrier.laurentInclusion (polyRef P d) (chart P d) (laurentRef P d)
    (ordinary P d) (shifted P d)).comp
    ((mapParameter (anchorNode
      (LaurentUnitReferenceSpecialization.commonUnit P (firstArrow d) (secondArrow d)))).comp
      (parameter (laurentRef P d) (BassH0Merge.nodes P (firstArrow d) (secondArrow d))))

/-- The complete original oldPositive scalar rail on the minus sheet. -/
abbrev oldPositiveMinus :=
  (ProjectionRectangleParameters.D BassH0Diagram.plusFace).map (ordinaryMap P d).continuous

/-- The complete original positiveMovement scalar rail on the minus sheet. -/
abbrev positiveMovementMinus :=
  (ProjectionRectangleParameters.L BassH0Diagram.plusFace).map (ordinaryMap P d).continuous

/-- The complete original polynomialMovement scalar rail on the minus sheet. -/
abbrev polynomialMovementMinus :=
  (ProjectionRectangleParameters.Ppath BassH0Diagram.plusFace).map (ordinaryMap P d).continuous

/-- The complete original laurentMovement scalar rail on the minus sheet. -/
abbrev laurentMovementMinus :=
  (ProjectionRectangleParameters.T BassH0Diagram.plusFace).map (ordinaryMap P d).continuous

/-- The complete original newPositive scalar rail on the minus sheet. -/
abbrev newPositiveMinus :=
  (ProjectionRectangleParameters.K BassH0Diagram.plusFace).map (ordinaryMap P d).continuous

/-- The specified positive rectangle, with its original source and target path words. -/
def rectangleMinus :
    ((positiveMovementMinus P d).trans (polynomialMovementMinus P d)).Homotopy
      ((oldPositiveMinus P d).symm.trans
        ((laurentMovementMinus P d).trans (newPositiveMinus P d))) :=
  Path.Homotopy.mapProjectionRectangle (ordinaryMap P d)
    (ProjectionRectangleParameters.D BassH0Diagram.plusFace)
    (ProjectionRectangleParameters.L BassH0Diagram.plusFace)
    (ProjectionRectangleParameters.Ppath BassH0Diagram.plusFace)
    (ProjectionRectangleParameters.T BassH0Diagram.plusFace)
    (ProjectionRectangleParameters.K BassH0Diagram.plusFace)
    (ProjectionRectangleParameters.rectangle BassH0Diagram.plusFace)

/-- Both original rectangle coordinates remain unchanged throughout the interior. -/
theorem rectangleMinus_apply (r s : I) :
    rectangleMinus P d (r, s) = ordinaryMap P d
      (ProjectionRectangleParameters.rectangle BassH0Diagram.plusFace (r, s)) := rfl

/-- The entire source rail retains its original two-piece clock. -/
theorem rectangleMinus_zero (s : I) :
    rectangleMinus P d (0, s) =
      ((positiveMovementMinus P d).trans (polynomialMovementMinus P d)) s :=
  (rectangleMinus P d).map_zero_left s

/-- The entire target rail retains its original reversed positive and nested outer word. -/
theorem rectangleMinus_one (s : I) :
    rectangleMinus P d (1, s) =
      ((oldPositiveMinus P d).symm.trans
        ((laurentMovementMinus P d).trans (newPositiveMinus P d))) s :=
  (rectangleMinus P d).map_one_left s

/-- The complete left rail is fixed at the original common full-node vertex. -/
theorem rectangleMinus_left (r : I) :
    rectangleMinus P d (r, 0) =
      ((positiveMovementMinus P d).trans (polynomialMovementMinus P d)) 0 :=
  (rectangleMinus P d).prop' r 0 (Or.inl rfl)

/-- The complete right rail is fixed at the original terminal full-node vertex. -/
theorem rectangleMinus_right (r : I) :
    rectangleMinus P d (r, 1) =
      ((positiveMovementMinus P d).trans (polynomialMovementMinus P d)) 1 :=
  (rectangleMinus P d).prop' r 1 (Or.inr rfl)

/-- The complete original oldPositive scalar rail on the plus sheet. -/
abbrev oldPositivePlus :=
  (ProjectionRectangleParameters.D BassH0Diagram.plusFace).map (shiftedMap P d).continuous

/-- The complete original positiveMovement scalar rail on the plus sheet. -/
abbrev positiveMovementPlus :=
  (ProjectionRectangleParameters.L BassH0Diagram.plusFace).map (shiftedMap P d).continuous

/-- The complete original polynomialMovement scalar rail on the plus sheet. -/
abbrev polynomialMovementPlus :=
  (ProjectionRectangleParameters.Ppath BassH0Diagram.plusFace).map (shiftedMap P d).continuous

/-- The complete original laurentMovement scalar rail on the plus sheet. -/
abbrev laurentMovementPlus :=
  (ProjectionRectangleParameters.T BassH0Diagram.plusFace).map (shiftedMap P d).continuous

/-- The complete original newPositive scalar rail on the plus sheet. -/
abbrev newPositivePlus :=
  (ProjectionRectangleParameters.K BassH0Diagram.plusFace).map (shiftedMap P d).continuous

/-- The specified positive rectangle, with its original source and target path words. -/
def rectanglePlus :
    ((positiveMovementPlus P d).trans (polynomialMovementPlus P d)).Homotopy
      ((oldPositivePlus P d).symm.trans
        ((laurentMovementPlus P d).trans (newPositivePlus P d))) :=
  Path.Homotopy.mapProjectionRectangle (shiftedMap P d)
    (ProjectionRectangleParameters.D BassH0Diagram.plusFace)
    (ProjectionRectangleParameters.L BassH0Diagram.plusFace)
    (ProjectionRectangleParameters.Ppath BassH0Diagram.plusFace)
    (ProjectionRectangleParameters.T BassH0Diagram.plusFace)
    (ProjectionRectangleParameters.K BassH0Diagram.plusFace)
    (ProjectionRectangleParameters.rectangle BassH0Diagram.plusFace)

/-- Both original rectangle coordinates remain unchanged throughout the interior. -/
theorem rectanglePlus_apply (r s : I) :
    rectanglePlus P d (r, s) = shiftedMap P d
      (ProjectionRectangleParameters.rectangle BassH0Diagram.plusFace (r, s)) := rfl

/-- The entire source rail retains its original two-piece clock. -/
theorem rectanglePlus_zero (s : I) :
    rectanglePlus P d (0, s) =
      ((positiveMovementPlus P d).trans (polynomialMovementPlus P d)) s :=
  (rectanglePlus P d).map_zero_left s

/-- The entire target rail retains its original reversed positive and nested outer word. -/
theorem rectanglePlus_one (s : I) :
    rectanglePlus P d (1, s) =
      ((oldPositivePlus P d).symm.trans
        ((laurentMovementPlus P d).trans (newPositivePlus P d))) s :=
  (rectanglePlus P d).map_one_left s

/-- The complete left rail is fixed at the original common full-node vertex. -/
theorem rectanglePlus_left (r : I) :
    rectanglePlus P d (r, 0) =
      ((positiveMovementPlus P d).trans (polynomialMovementPlus P d)) 0 :=
  (rectanglePlus P d).prop' r 0 (Or.inl rfl)

/-- The complete right rail is fixed at the original terminal full-node vertex. -/
theorem rectanglePlus_right (r : I) :
    rectanglePlus P d (r, 1) =
      ((positiveMovementPlus P d).trans (polynomialMovementPlus P d)) 1 :=
  (rectanglePlus P d).prop' r 1 (Or.inr rfl)

/-- The ordinary polynomial rail is exactly the whole lower edge of its own cone square. -/
theorem polynomialMinus_seam (s : I) :
    polynomialMovementMinus P d s = (coneSquareMinus P d).parameter (s, 0) := by
  change CutOpenCarrier.laurentInclusion (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d)
      (parameter (laurentRef P d) (BassH0Merge.nodes P (firstArrow d) (secondArrow d))
        (ProjectionRectangleParameters.Ppath BassH0Diagram.plusFace s)) =
    CutOpenCarrier.cylinderMinus (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) (movement P d s, 0)
  rw [CutOpenCarrier.cylinderMinus_zero,
    CoefficientBassPositiveJ0PolynomialAttachment.movement_attach]
  rfl

/-- The shifted polynomial rail meets its separate cylinder with the full commonUnit anchor. -/
theorem polynomialPlus_seam (s : I) :
    polynomialMovementPlus P d s = (coneSquarePlus P d).parameter (s, 0) :=
  (CoefficientBassPositiveJ0ShiftedPolynomial.shifted_seam P d s).symm

/-- Both endpoint joins follow from the entire polynomial/cone seam, without tip merging. -/
theorem polynomialMinus_cone_base (s : I) :
    polynomialMovementMinus P d s = conePathMinus P d s 0 :=
  polynomialMinus_seam P d s

/-- Both endpoint joins follow from the entire polynomial/cone seam, without tip merging. -/
theorem polynomialPlus_cone_base (s : I) :
    polynomialMovementPlus P d s = conePathPlus P d s 0 :=
  polynomialPlus_seam P d s

/-- The entire minus rectangle has its exact full-reference native family at every level. -/
theorem rectangleMinus_native_parameter (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (rectangleMinus P d (r, s)) x =
    (LoopPrespectrum.mappingConeInclusion (prespectrumMap (chart P d))).map n
      (prespectrumFamily (laurentRef P d)
        (BassH0Merge.nodes P (firstArrow d) (secondArrow d)) n
        (ProjectionRectangleParameters.rectangle BassH0Diagram.plusFace (r, s), x)) := by
  rw [rectangleMinus_apply]
  change CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n
      (CutOpenCarrier.laurentInclusion (polyRef P d) (chart P d) (laurentRef P d)
        (ordinary P d) (shifted P d) _) x = _
  rw [CutOpenCarrier.nativeEval_laurentInclusion,
    pointwisePrespectrumFamily_parameter]

/-- The entire plus rectangle has its exact full-reference native family at every level. -/
theorem rectanglePlus_native_parameter (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (rectanglePlus P d (r, s)) x =
    (LoopPrespectrum.mappingConeInclusion (prespectrumMap (chart P d))).map n
      (prespectrumFamily (laurentRef P d)
        (fun i ↦ anchorNode
          (LaurentUnitReferenceSpecialization.commonUnit P (firstArrow d) (secondArrow d))
          (BassH0Merge.nodes P (firstArrow d) (secondArrow d) i)) n
        (ProjectionRectangleParameters.rectangle BassH0Diagram.plusFace (r, s), x)) := by
  rw [rectanglePlus_apply]
  change CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n
      (CutOpenCarrier.laurentInclusion (polyRef P d) (chart P d) (laurentRef P d)
        (ordinary P d) (shifted P d) _) x = _
  rw [CutOpenCarrier.nativeEval_laurentInclusion, ContinuousMap.comp_apply,
    mapParameter_parameter, pointwisePrespectrumFamily_parameter]

end Quillen.PerfectComplexes.CoefficientBassPositiveJ0Rectangles
