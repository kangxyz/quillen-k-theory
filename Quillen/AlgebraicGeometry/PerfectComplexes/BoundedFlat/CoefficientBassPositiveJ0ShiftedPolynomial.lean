/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveJ0PolynomialAttachment
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
namespace Quillen.PerfectComplexes.CoefficientBassPositiveJ0ShiftedPolynomial
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

variable {R : CommRingCat.{u}} (P : Over (Spec R)) (d : Under R)
/-- The actual first coefficient arrow, without notation quotation. -/
abbrev chosenP := (polynomialUnderCoefficient R).app d
/-- The actual positive Laurent chart arrow, without notation quotation. -/
abbrev chosenQ := (underToLaurent R).app d
/-- The unchanged chosen polynomial reference. -/
abbrev chosenF := CoefficientBassPositiveJ0PolynomialMovement.reference P d
/-- The unchanged common Laurent reference. -/
abbrev chosenG := laurentReference P (chosenP d) (chosenQ d)
/-- The original target positive chart model map. -/
abbrev chosenJ := chartMap P (c := (laurentUnderFunctor R).obj d)
/-- The original forward unit on the common Laurent reference. -/
abbrev chosenUnit := LaurentUnitReferenceSpecialization.commonUnit P (chosenP d) (chosenQ d)
/-- The original ordinary attachment isomorphism. -/
abbrev chosenOrdinary := ordinaryAnchor P (chosenP d) (chosenQ d)
/-- The original unit-shifted attachment isomorphism. -/
abbrev chosenShifted :=
  LaurentUnitReferenceSpecialization.shiftedAnchor P (chosenP d) (chosenQ d)
/-- The whole polynomial movement with its original clock. -/
abbrev chosenPath := CoefficientBassPositiveJ0PolynomialMovement.movement P d
/-- The complete five-node polynomial movement family. -/
abbrev chosenNodes := CoefficientBassPositiveJ0PolynomialMovement.nodes P d

/-- The original forward unit is conjugated through the entire ordinary attachment reference. -/
theorem shifted_anchor_action : (chosenShifted P d) = (chosenOrdinary P d) ≪≫
    Quillen.FunctorIdentityAutomorphism.onFunctor ((chosenF P d) ≫ (chosenJ P d)).functor
      (LaurentUnitReferenceSpecialization.smallUnit P ((laurentUnderFunctor R).obj d)) :=
  LaurentUnitReferenceSpecialization.shiftedAnchor_eq_target_action P (chosenP d) (chosenQ d)

/-- Every complete polynomial reference uses the prescribed shifted attachment. -/
theorem shifted_nodes (i : Fin 5) :
    anchorNode (chosenUnit P d) (ordinaryAttachNode P (chosenP d) (chosenQ d) ((chosenNodes P d)
      i)) = shiftedAttachNode P (chosenP d) (chosenQ d) ((chosenNodes P d) i) :=
  shift_attach (chosenF P d) (chosenJ P d) (chosenG P d) (chosenUnit P d) (chosenOrdinary P d)
      ((chosenNodes P d) i)

/-- All five raw positive-row references shift through the same source-unit action. -/
theorem shifted_raw_nodes (i : Fin 5) :
    anchorNode (chosenUnit P d) (BassH0Merge.nodes P (chosenP d) (chosenQ d)
      (BassH0Diagram.plusFace.toOrderHom
      (ProjectionRectangleSquareRows.polynomialRow i))) = shiftedAttachNode P (chosenP d) (chosenQ
      d) ((chosenNodes P d) i) :=
  (congrArg (anchorNode (chosenUnit P d))
    (CoefficientBassPositiveJ0PolynomialAttachment.full_nodes P d i)).trans (shifted_nodes P d i)

/-- The complete shifted Laurent boundary retains the original Ppath and polynomial input. -/
theorem shifted_movement_attach (r : I) :
    mapParameter (anchorNode (chosenUnit P d)) (parameter (chosenG P d) (BassH0Merge.nodes P
      (chosenP d) (chosenQ d))
      (ProjectionRectangleParameters.Ppath BassH0Diagram.plusFace r)) =
    mapParameter (shiftedAttachNode P (chosenP d) (chosenQ d)) ((chosenPath P d) r) := by
  rw [CoefficientBassPositiveJ0PolynomialAttachment.movement_attach]
  change mapParameter (anchorNode (chosenUnit P d))
      (mapParameter (ordinaryAttachNode P (chosenP d) (chosenQ d))
        (parameter (chosenF P d) (chosenNodes P d) (NativeSquareFiveSimplex.parameter r))) =
    mapParameter (shiftedAttachNode P (chosenP d) (chosenQ d))
      (parameter (chosenF P d) (chosenNodes P d) (NativeSquareFiveSimplex.parameter r))
  rw [mapParameter_parameter, mapParameter_parameter, mapParameter_parameter]
  exact congrArg (fun ns : Fin 5 → Node (chosenG P d) ↦
    parameter (chosenG P d) ns (NativeSquareFiveSimplex.parameter r)) (funext (shifted_nodes P d))

/-- The second actual cylinder meets exactly this shifted raw Laurent boundary. -/
theorem shifted_seam (r : I) :
    CutOpenCarrier.cylinderPlus (chosenF P d) (chosenJ P d) (chosenG P d) (chosenOrdinary P d)
      (chosenShifted P d) ((chosenPath P d) r, 0) =
    CutOpenCarrier.laurentInclusion (chosenF P d) (chosenJ P d) (chosenG P d) (chosenOrdinary P d)
      (chosenShifted P d)
      (mapParameter (anchorNode (chosenUnit P d)) (parameter (chosenG P d) (BassH0Merge.nodes P
      (chosenP d) (chosenQ d))
        (ProjectionRectangleParameters.Ppath BassH0Diagram.plusFace r))) := by
  rw [CutOpenCarrier.cylinderPlus_zero, shifted_movement_attach]
  rfl

/-- The interior is the original independent-time native polynomial/cone interchange. -/
theorem shifted_cylinder_native (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (chosenF P d) (chosenJ P d) (chosenG P d) (chosenOrdinary P d)
      (chosenShifted P d) n
      (CutOpenCarrier.cylinderPlus (chosenF P d) (chosenJ P d) (chosenG P d) (chosenOrdinary P d)
      (chosenShifted P d) ((chosenPath P d) r, s)) x =
    (LoopPrespectrum.Homotopy.Square.interchange
      (boundedFlatCoefficientPolynomialSquareHomotopy P
        (CoefficientBassPositiveJ0PolynomialMovement.arrow d))
      (LoopPrespectrum.mappingConeHomotopy (prespectrumMap (chosenJ P d)))).level n (r, (s, x)) :=
      by
  rw [CutOpenCarrier.nativeEval_cylinderPlus,
    CoefficientBassPositiveJ0PolynomialMovement.movement_native]
  rfl

/-- The shifted cylinder terminates at its own original tip. -/
theorem shifted_tip (r : I) :
    CutOpenCarrier.cylinderPlus (chosenF P d) (chosenJ P d) (chosenG P d) (chosenOrdinary P d)
      (chosenShifted P d) ((chosenPath P d) r, 1) =
      CutOpenCarrier.tipPlus (chosenF P d) (chosenJ P d) (chosenG P d) (chosenOrdinary P d)
      (chosenShifted P d) :=
  CutOpenCarrier.cylinderPlus_one (chosenF P d) (chosenJ P d) (chosenG P d) (chosenOrdinary P d)
      (chosenShifted P d) ((chosenPath P d) r)

/-- The unchanged polynomial input does not identify the two actual terminal tips. -/
theorem distinct_terminal_tips :
    CutOpenCarrier.tipMinus (chosenF P d) (chosenJ P d) (chosenG P d) (chosenOrdinary P d)
      (chosenShifted P d) ≠ CutOpenCarrier.tipPlus (chosenF P d) (chosenJ P d) (chosenG P d)
      (chosenOrdinary P d) (chosenShifted P d) :=
  CutOpenCarrier.tips_ne (chosenF P d) (chosenJ P d) (chosenG P d) (chosenOrdinary P d)
      (chosenShifted P d)

end Quillen.PerfectComplexes.CoefficientBassPositiveJ0ShiftedPolynomial
