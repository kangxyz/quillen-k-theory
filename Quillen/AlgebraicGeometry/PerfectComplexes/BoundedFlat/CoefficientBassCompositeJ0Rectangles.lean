/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeJ0ConeBoundaries
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
namespace Quillen.PerfectComplexes.CoefficientBassCompositeJ0Rectangles
open CommonReferenceNerve BassH0Merge CoefficientBassCompositeJ0ConeBoundaries
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The unchanged two-tip carrier with both specified attachment references. -/
abbrev Carrier := CutOpenCarrier.space (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
  (ordinary P p q) (shifted P p q)

/-- The entire ordinary full-node Laurent simplex, included in the actual carrier. -/
def ordinaryMap : C(StdSimplex ℝ (Fin 31), Carrier P p q) :=
  (CutOpenCarrier.laurentInclusion (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
    (ordinary P p q) (shifted P p q)).comp
    (parameter (laurentRef P p q) (BassH0Merge.nodes P p q))

/-- The entire shifted full-node simplex uses the original commonUnit action. -/
def shiftedMap : C(StdSimplex ℝ (Fin 31), Carrier P p q) :=
  (CutOpenCarrier.laurentInclusion (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
    (ordinary P p q) (shifted P p q)).comp
    ((mapParameter (anchorNode
      (LaurentUnitReferenceSpecialization.commonUnit P p q))).comp
      (parameter (laurentRef P p q) (BassH0Merge.nodes P p q)))

/-- The complete original oldPositive scalar rail on the minus sheet. -/
abbrev oldPositiveMinus :=
  (ProjectionRectangleParameters.D BassH0Diagram.plusFace).map (ordinaryMap P p q).continuous

/-- The complete original positiveMovement scalar rail on the minus sheet. -/
abbrev positiveMovementMinus :=
  (ProjectionRectangleParameters.L BassH0Diagram.plusFace).map (ordinaryMap P p q).continuous

/-- The complete original polynomialMovement scalar rail on the minus sheet. -/
abbrev polynomialMovementMinus :=
  (ProjectionRectangleParameters.Ppath BassH0Diagram.plusFace).map (ordinaryMap P p q).continuous

/-- The complete original laurentMovement scalar rail on the minus sheet. -/
abbrev laurentMovementMinus :=
  (ProjectionRectangleParameters.T BassH0Diagram.plusFace).map (ordinaryMap P p q).continuous

/-- The complete original newPositive scalar rail on the minus sheet. -/
abbrev newPositiveMinus :=
  (ProjectionRectangleParameters.K BassH0Diagram.plusFace).map (ordinaryMap P p q).continuous

/-- The specified positive rectangle, with its original source and target path words. -/
def rectangleMinus :
    ((positiveMovementMinus P p q).trans (polynomialMovementMinus P p q)).Homotopy
      ((oldPositiveMinus P p q).symm.trans
        ((laurentMovementMinus P p q).trans (newPositiveMinus P p q))) :=
  Path.Homotopy.mapProjectionRectangle (ordinaryMap P p q)
    (ProjectionRectangleParameters.D BassH0Diagram.plusFace)
    (ProjectionRectangleParameters.L BassH0Diagram.plusFace)
    (ProjectionRectangleParameters.Ppath BassH0Diagram.plusFace)
    (ProjectionRectangleParameters.T BassH0Diagram.plusFace)
    (ProjectionRectangleParameters.K BassH0Diagram.plusFace)
    (ProjectionRectangleParameters.rectangle BassH0Diagram.plusFace)

/-- Both original rectangle coordinates remain unchanged throughout the interior. -/
theorem rectangleMinus_apply (r s : I) :
    rectangleMinus P p q (r, s) = ordinaryMap P p q
      (ProjectionRectangleParameters.rectangle BassH0Diagram.plusFace (r, s)) := rfl

/-- The entire source rail retains its original two-piece clock. -/
theorem rectangleMinus_zero (s : I) :
    rectangleMinus P p q (0, s) =
      ((positiveMovementMinus P p q).trans (polynomialMovementMinus P p q)) s :=
  (rectangleMinus P p q).map_zero_left s

/-- The entire target rail retains its original reversed positive and nested outer word. -/
theorem rectangleMinus_one (s : I) :
    rectangleMinus P p q (1, s) =
      ((oldPositiveMinus P p q).symm.trans
        ((laurentMovementMinus P p q).trans (newPositiveMinus P p q))) s :=
  (rectangleMinus P p q).map_one_left s

/-- The complete left rail is fixed at the original common full-node vertex. -/
theorem rectangleMinus_left (r : I) :
    rectangleMinus P p q (r, 0) =
      ((positiveMovementMinus P p q).trans (polynomialMovementMinus P p q)) 0 :=
  (rectangleMinus P p q).prop' r 0 (Or.inl rfl)

/-- The complete right rail is fixed at the original terminal full-node vertex. -/
theorem rectangleMinus_right (r : I) :
    rectangleMinus P p q (r, 1) =
      ((positiveMovementMinus P p q).trans (polynomialMovementMinus P p q)) 1 :=
  (rectangleMinus P p q).prop' r 1 (Or.inr rfl)

/-- The complete original oldPositive scalar rail on the plus sheet. -/
abbrev oldPositivePlus :=
  (ProjectionRectangleParameters.D BassH0Diagram.plusFace).map (shiftedMap P p q).continuous

/-- The complete original positiveMovement scalar rail on the plus sheet. -/
abbrev positiveMovementPlus :=
  (ProjectionRectangleParameters.L BassH0Diagram.plusFace).map (shiftedMap P p q).continuous

/-- The complete original polynomialMovement scalar rail on the plus sheet. -/
abbrev polynomialMovementPlus :=
  (ProjectionRectangleParameters.Ppath BassH0Diagram.plusFace).map (shiftedMap P p q).continuous

/-- The complete original laurentMovement scalar rail on the plus sheet. -/
abbrev laurentMovementPlus :=
  (ProjectionRectangleParameters.T BassH0Diagram.plusFace).map (shiftedMap P p q).continuous

/-- The complete original newPositive scalar rail on the plus sheet. -/
abbrev newPositivePlus :=
  (ProjectionRectangleParameters.K BassH0Diagram.plusFace).map (shiftedMap P p q).continuous

/-- The specified positive rectangle, with its original source and target path words. -/
def rectanglePlus :
    ((positiveMovementPlus P p q).trans (polynomialMovementPlus P p q)).Homotopy
      ((oldPositivePlus P p q).symm.trans
        ((laurentMovementPlus P p q).trans (newPositivePlus P p q))) :=
  Path.Homotopy.mapProjectionRectangle (shiftedMap P p q)
    (ProjectionRectangleParameters.D BassH0Diagram.plusFace)
    (ProjectionRectangleParameters.L BassH0Diagram.plusFace)
    (ProjectionRectangleParameters.Ppath BassH0Diagram.plusFace)
    (ProjectionRectangleParameters.T BassH0Diagram.plusFace)
    (ProjectionRectangleParameters.K BassH0Diagram.plusFace)
    (ProjectionRectangleParameters.rectangle BassH0Diagram.plusFace)

/-- Both original rectangle coordinates remain unchanged throughout the interior. -/
theorem rectanglePlus_apply (r s : I) :
    rectanglePlus P p q (r, s) = shiftedMap P p q
      (ProjectionRectangleParameters.rectangle BassH0Diagram.plusFace (r, s)) := rfl

/-- The entire source rail retains its original two-piece clock. -/
theorem rectanglePlus_zero (s : I) :
    rectanglePlus P p q (0, s) =
      ((positiveMovementPlus P p q).trans (polynomialMovementPlus P p q)) s :=
  (rectanglePlus P p q).map_zero_left s

/-- The entire target rail retains its original reversed positive and nested outer word. -/
theorem rectanglePlus_one (s : I) :
    rectanglePlus P p q (1, s) =
      ((oldPositivePlus P p q).symm.trans
        ((laurentMovementPlus P p q).trans (newPositivePlus P p q))) s :=
  (rectanglePlus P p q).map_one_left s

/-- The complete left rail is fixed at the original common full-node vertex. -/
theorem rectanglePlus_left (r : I) :
    rectanglePlus P p q (r, 0) =
      ((positiveMovementPlus P p q).trans (polynomialMovementPlus P p q)) 0 :=
  (rectanglePlus P p q).prop' r 0 (Or.inl rfl)

/-- The complete right rail is fixed at the original terminal full-node vertex. -/
theorem rectanglePlus_right (r : I) :
    rectanglePlus P p q (r, 1) =
      ((positiveMovementPlus P p q).trans (polynomialMovementPlus P p q)) 1 :=
  (rectanglePlus P p q).prop' r 1 (Or.inr rfl)

/-- The ordinary polynomial rail is exactly the whole lower edge of its own cone square. -/
theorem polynomialMinus_seam (s : I) :
    polynomialMovementMinus P p q s = (coneSquareMinus P p q).parameter (s, 0) := by
  change CutOpenCarrier.laurentInclusion (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q)
      (parameter (laurentRef P p q) (BassH0Merge.nodes P p q)
        (ProjectionRectangleParameters.Ppath BassH0Diagram.plusFace s)) =
    CutOpenCarrier.cylinderMinus (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) (movement P p q s, 0)
  rw [CutOpenCarrier.cylinderMinus_zero,
    CoefficientBassCompositeJ0Attachment.movement_attach]
  rfl

/-- The shifted polynomial rail meets its separate cylinder with the full commonUnit anchor. -/
theorem polynomialPlus_seam (s : I) :
    polynomialMovementPlus P p q s = (coneSquarePlus P p q).parameter (s, 0) :=
  (CoefficientBassCompositeJ0ShiftedPolynomial.shifted_seam P p q s).symm

/-- Both endpoint joins follow from the entire polynomial/cone seam, without tip merging. -/
theorem polynomialMinus_cone_base (s : I) :
    polynomialMovementMinus P p q s = conePathMinus P p q s 0 :=
  polynomialMinus_seam P p q s

/-- Both endpoint joins follow from the entire polynomial/cone seam, without tip merging. -/
theorem polynomialPlus_cone_base (s : I) :
    polynomialMovementPlus P p q s = conePathPlus P p q s 0 :=
  polynomialPlus_seam P p q s

/-- The entire minus rectangle has its exact full-reference native family at every level. -/
theorem rectangleMinus_native_parameter (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n (rectangleMinus P p q (r, s)) x =
    (LoopPrespectrum.mappingConeInclusion (prespectrumMap (chart P (c := c)))).map n
      (prespectrumFamily (laurentRef P p q)
        (BassH0Merge.nodes P p q) n
        (ProjectionRectangleParameters.rectangle BassH0Diagram.plusFace (r, s), x)) := by
  rw [rectangleMinus_apply]
  change CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n
      (CutOpenCarrier.laurentInclusion (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
        (ordinary P p q) (shifted P p q) _) x = _
  rw [CutOpenCarrier.nativeEval_laurentInclusion,
    pointwisePrespectrumFamily_parameter]

/-- The entire plus rectangle has its exact full-reference native family at every level. -/
theorem rectanglePlus_native_parameter (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n (rectanglePlus P p q (r, s)) x =
    (LoopPrespectrum.mappingConeInclusion (prespectrumMap (chart P (c := c)))).map n
      (prespectrumFamily (laurentRef P p q)
        (fun i ↦ anchorNode
          (LaurentUnitReferenceSpecialization.commonUnit P p q)
          (BassH0Merge.nodes P p q i)) n
        (ProjectionRectangleParameters.rectangle BassH0Diagram.plusFace (r, s), x)) := by
  rw [rectanglePlus_apply]
  change CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) n
      (CutOpenCarrier.laurentInclusion (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
        (ordinary P p q) (shifted P p q) _) x = _
  rw [CutOpenCarrier.nativeEval_laurentInclusion, ContinuousMap.comp_apply,
    mapParameter_parameter, pointwisePrespectrumFamily_parameter]

end Quillen.PerfectComplexes.CoefficientBassCompositeJ0Rectangles
