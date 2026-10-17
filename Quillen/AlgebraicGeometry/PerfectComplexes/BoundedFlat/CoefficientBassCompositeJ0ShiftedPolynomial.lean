/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeJ0Attachment
public import Quillen.Topology.Prespectrum.HomotopySquareInterchange

/-!
# The same polynomial movement with the original shifted Laurent attachment

The polynomial path is unchanged. The second cylinder attaches through the original common
Laurent unit, rather than a new polynomial unit. Full references and the original clock are
retained, and its own tip remains distinct from the first cylinder's tip.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u v
namespace Quillen.PerfectComplexes.CoefficientBassCompositeJ0ShiftedPolynomial
open CommonReferenceNerve BassH0Merge
open CoefficientBassPositiveC1BoundaryLift CoefficientBassPositiveC0CarrierAttachment

private theorem shift_attach {V W T : Model.{v}} (F : V ⟶ W) (J : W ⟶ T) (G : V ⟶ T)
    (τ : G.functor ≅ G.functor) (ε : G.functor ≅ (F ≫ J).functor) (N : Node F) :
    anchorNode τ (attachPostcompNode F J G ε N) =
      attachPostcompNode F J G (τ ≪≫ ε) N := by
  rcases N with ⟨K, ρ⟩
  change (⟨K ≫ J, τ ≪≫ (ε ≪≫ isoWhiskerRight ρ J.functor)⟩ : Node G) =
    ⟨K ≫ J, (τ ≪≫ ε) ≪≫ isoWhiskerRight ρ J.functor⟩
  exact congrArg (fun η : G.functor ≅ (K ≫ J).functor ↦ (⟨K ≫ J, η⟩ : Node G))
    (Iso.trans_assoc τ ε (isoWhiskerRight ρ J.functor)).symm

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)
/-- The unchanged chosen polynomial reference. -/
abbrev chosenF := CoefficientBassCompositeJ0Polynomial.reference P p q
/-- The unchanged common Laurent reference. -/
abbrev chosenG := laurentReference P p q
/-- The original forward unit on the common Laurent reference. -/
abbrev chosenUnit := LaurentUnitReferenceSpecialization.commonUnit P p q
/-- The original ordinary attachment isomorphism. -/
abbrev chosenOrdinary := ordinaryAnchor P p q
/-- The original unit-shifted attachment isomorphism. -/
abbrev chosenShifted :=
  LaurentUnitReferenceSpecialization.shiftedAnchor P p q
/-- The whole polynomial movement with its original clock. -/
abbrev chosenPath := CoefficientBassCompositeJ0Polynomial.movement P p q
/-- The complete five-node polynomial movement family. -/
abbrev chosenNodes := CoefficientBassCompositeJ0Polynomial.nodes P p q

/-- The original forward unit is conjugated through the entire ordinary attachment reference. -/
theorem shifted_anchor_action : (chosenShifted P p q) = (chosenOrdinary P p q) ≪≫
    Quillen.FunctorIdentityAutomorphism.onFunctor ((chosenF P p q) ≫ (chartMap P (c := c))).functor
      (LaurentUnitReferenceSpecialization.smallUnit P c) :=
  LaurentUnitReferenceSpecialization.shiftedAnchor_eq_target_action P p q

/-- Every complete polynomial reference uses the prescribed shifted attachment. -/
theorem shifted_nodes (i : Fin 5) :
    anchorNode (chosenUnit P p q) (ordinaryAttachNode P p q ((chosenNodes P p q)
      i)) = shiftedAttachNode P p q ((chosenNodes P p q) i) :=
  shift_attach (chosenF P p q) (chartMap P (c := c)) (chosenG P p q) (chosenUnit P p q)
      (chosenOrdinary P p q)
      ((chosenNodes P p q) i)

/-- All five raw positive-row references shift through the same source-unit action. -/
theorem shifted_raw_nodes (i : Fin 5) :
    anchorNode (chosenUnit P p q) (BassH0Merge.nodes P p q
      (BassH0Diagram.plusFace.toOrderHom
      (ProjectionRectangleSquareRows.polynomialRow i))) = shiftedAttachNode P p q ((chosenNodes P
          p q) i) :=
  (congrArg (anchorNode (chosenUnit P p q))
    (CoefficientBassCompositeJ0Attachment.full_nodes P p q i)).trans (shifted_nodes P p q i)

/-- The complete shifted Laurent boundary retains the original Ppath and polynomial input. -/
theorem shifted_movement_attach (r : I) :
    mapParameter (anchorNode (chosenUnit P p q)) (parameter (chosenG P p q) (BassH0Merge.nodes P
      p q)
      (ProjectionRectangleParameters.Ppath BassH0Diagram.plusFace r)) =
    mapParameter (shiftedAttachNode P p q) ((chosenPath P p q) r) := by
  rw [CoefficientBassCompositeJ0Attachment.movement_attach]
  change mapParameter (anchorNode (chosenUnit P p q))
      (mapParameter (ordinaryAttachNode P p q)
        (parameter (chosenF P p q) (chosenNodes P p q) (NativeSquareFiveSimplex.parameter r))) =
    mapParameter (shiftedAttachNode P p q)
      (parameter (chosenF P p q) (chosenNodes P p q) (NativeSquareFiveSimplex.parameter r))
  rw [mapParameter_parameter, mapParameter_parameter, mapParameter_parameter]
  exact congrArg (fun ns : Fin 5 → Node (chosenG P p q) ↦
    parameter (chosenG P p q) ns (NativeSquareFiveSimplex.parameter r)) (funext (shifted_nodes P p
        q))

/-- The second actual cylinder meets exactly this shifted raw Laurent boundary. -/
theorem shifted_seam (r : I) :
    CutOpenCarrier.cylinderPlus (chosenF P p q) (chartMap P (c := c)) (chosenG P p q)
        (chosenOrdinary P p q)
      (chosenShifted P p q) ((chosenPath P p q) r, 0) =
    CutOpenCarrier.laurentInclusion (chosenF P p q) (chartMap P (c := c)) (chosenG P p q)
        (chosenOrdinary P p q)
      (chosenShifted P p q)
      (mapParameter (anchorNode (chosenUnit P p q)) (parameter (chosenG P p q) (BassH0Merge.nodes P
      p q)
        (ProjectionRectangleParameters.Ppath BassH0Diagram.plusFace r))) := by
  rw [CutOpenCarrier.cylinderPlus_zero, shifted_movement_attach]
  rfl

/-- The interior is the original independent-time native polynomial/cone interchange. -/
theorem shifted_cylinder_native (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CutOpenCarrier.nativeEval (chosenF P p q) (chartMap P (c := c)) (chosenG P p q)
        (chosenOrdinary P p q)
      (chosenShifted P p q) n
      (CutOpenCarrier.cylinderPlus (chosenF P p q) (chartMap P (c := c)) (chosenG P p q)
          (chosenOrdinary P p q)
      (chosenShifted P p q) ((chosenPath P p q) r, s)) x =
    (LoopPrespectrum.Homotopy.Square.interchange
      (boundedFlatCoefficientPolynomialSquareHomotopy P
        (CoefficientBassCompositeJ0Polynomial.arrow p q))
      (LoopPrespectrum.mappingConeHomotopy (prespectrumMap (chartMap P (c := c))))).level n (r,
          (s, x)) :=
      by
  rw [CutOpenCarrier.nativeEval_cylinderPlus,
    CoefficientBassCompositeJ0Polynomial.movement_native]
  rfl

/-- The shifted cylinder terminates at its own original tip. -/
theorem shifted_tip (r : I) :
    CutOpenCarrier.cylinderPlus (chosenF P p q) (chartMap P (c := c)) (chosenG P p q)
        (chosenOrdinary P p q)
      (chosenShifted P p q) ((chosenPath P p q) r, 1) =
      CutOpenCarrier.tipPlus (chosenF P p q) (chartMap P (c := c)) (chosenG P p q) (chosenOrdinary
          P p q)
      (chosenShifted P p q) :=
  CutOpenCarrier.cylinderPlus_one (chosenF P p q) (chartMap P (c := c)) (chosenG P p q)
      (chosenOrdinary P p q)
      (chosenShifted P p q) ((chosenPath P p q) r)

/-- The unchanged polynomial input does not identify the two actual terminal tips. -/
theorem distinct_terminal_tips :
    CutOpenCarrier.tipMinus (chosenF P p q) (chartMap P (c := c)) (chosenG P p q) (chosenOrdinary
        P p q)
      (chosenShifted P p q) ≠ CutOpenCarrier.tipPlus (chosenF P p q) (chartMap P (c := c))
          (chosenG P p q)
      (chosenOrdinary P p q) (chosenShifted P p q) :=
  CutOpenCarrier.tips_ne (chosenF P p q) (chartMap P (c := c)) (chosenG P p q) (chosenOrdinary P p
      q)
      (chosenShifted P p q)

end Quillen.PerfectComplexes.CoefficientBassCompositeJ0ShiftedPolynomial
