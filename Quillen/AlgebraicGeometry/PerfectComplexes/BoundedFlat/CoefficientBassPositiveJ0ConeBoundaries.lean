/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveJ0ShiftedPolynomial
public import
      Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveNullTrack
public import Quillen.Topology.Path.CarrierSquareBoundaryEvaluation

/-!
# Actual two-tip carrier cone boundaries and their full native images

Each original cylinder supplies its own complete square and endpoint paths. Boundary
extraction and terminal-pause cancellation use the unchanged generic clock. Evaluation is
proved from the whole polynomial movement and original cylinder formula. Identification
of the final path-level cancellation with the prespectrum conePasting transport is separate.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveJ0ConeBoundaries
open CommonReferenceNerve CoefficientBassPositiveC1BoundaryLift
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (d : Under R)
/-- The original polynomial coefficient arrow. -/
abbrev firstArrow := (polynomialUnderCoefficient R).app d
/-- The original positive Laurent chart arrow. -/
abbrev secondArrow := (underToLaurent R).app d
/-- The same chosen polynomial reference used by the actual carrier. -/
abbrev polyRef := CoefficientBassPositiveJ0PolynomialMovement.reference P d
/-- The same chosen common Laurent reference. -/
abbrev laurentRef := laurentReference P (firstArrow d) (secondArrow d)
/-- The original target positive chart model map. -/
abbrev chart := chartMap P (c := (laurentUnderFunctor R).obj d)
/-- The actual ordinary attachment isomorphism. -/
abbrev ordinary := ordinaryAnchor P (firstArrow d) (secondArrow d)
/-- The actual forward-unit shifted attachment isomorphism. -/
abbrev shifted :=
  LaurentUnitReferenceSpecialization.shiftedAnchor P (firstArrow d) (secondArrow d)
/-- The entire original polynomial movement with its unchanged clock. -/
abbrev movement := CoefficientBassPositiveJ0PolynomialMovement.movement P d
/-- The original direct Laurent coefficient arrow. -/
abbrev arrow := CoefficientBassPositiveJ0PolynomialMovement.arrow d
/-- The original full polynomial and mapping-cone interchange square. -/
abbrev nativeInterchange := LoopPrespectrum.Homotopy.Square.interchange
  (boundedFlatCoefficientPolynomialSquareHomotopy P (arrow d))
  (LoopPrespectrum.mappingConeHomotopy (prespectrumMap (chart P d)))

/-- The original old cone path at an arbitrary native level and source point. -/
abbrev nativeOld (n : ℕ)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :=
  (CoefficientBassPositiveNullTrack.oldCone P (arrow d)).path n x

/-- The original new cone path, retaining its original endpoint casts. -/
abbrev nativeNew (n : ℕ)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :=
  (CoefficientBassPositiveNullTrack.newCone P (arrow d)).path n x

/-- The original polynomial movement followed by chart and cone inclusion. -/
abbrev nativeMove (n : ℕ)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :=
  (CoefficientBassPositiveNullTrack.polynomialMovement P (arrow d)).path n x

/-- The target square is the existing native interchange, evaluated at a fixed source point. -/
def nativeSquare (n : ℕ)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CarrierPathSquare.Square (nativeOld P d n x) (nativeNew P d n x)
      (nativeMove P d n x) (Path.refl ((CutOpenCarrier.nativeCone (chart P d)).point n)) where
  parameter := ⟨fun z ↦ (nativeInterchange P d).level n (z.1, (z.2, x)), by fun_prop⟩
  at_zero s := (nativeInterchange P d).at_zero n s x
  at_one s := (nativeInterchange P d).at_one n s x
  left r := (nativeInterchange P d).left n r x
  right r := (nativeInterchange P d).right n r x

/-- The entire minus cylinder over one polynomial input, with its own actual tip. -/
def conePathMinus (r : I) : Path
    (CutOpenCarrier.cylinderMinus (polyRef P d) (chart P d) (laurentRef P d) (ordinary P d)
      (shifted P d) (movement P d r, 0))
    (CutOpenCarrier.tipMinus (polyRef P d) (chart P d) (laurentRef P d) (ordinary P d) (shifted P
      d)) where
  toFun s := CutOpenCarrier.cylinderMinus (polyRef P d) (chart P d) (laurentRef P d) (ordinary P
      d) (shifted P d) (movement P d r, s)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := CutOpenCarrier.cylinderMinus_one (polyRef P d) (chart P d) (laurentRef P d) (ordinary
      P d) (shifted P d) (movement P d r)

/-- The complete attached polynomial edge, with unchanged original movement time. -/
def movementEdgeMinus : Path
    (CutOpenCarrier.cylinderMinus (polyRef P d) (chart P d) (laurentRef P d) (ordinary P d)
      (shifted P d) (movement P d 0, 0))
    (CutOpenCarrier.cylinderMinus (polyRef P d) (chart P d) (laurentRef P d) (ordinary P d)
      (shifted P d) (movement P d 1, 0)) where
  toFun r := CutOpenCarrier.cylinderMinus (polyRef P d) (chart P d) (laurentRef P d) (ordinary P
      d) (shifted P d) (movement P d r, 0)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

/-- The actual minus cone square, with all four original whole edges. -/
def coneSquareMinus : CarrierPathSquare.Square
    (conePathMinus P d 0) (conePathMinus P d 1) (movementEdgeMinus P d)
    (Path.refl (CutOpenCarrier.tipMinus (polyRef P d) (chart P d) (laurentRef P d) (ordinary P d)
      (shifted P d))) where
  parameter := ⟨fun z ↦ CutOpenCarrier.cylinderMinus (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d)
    (movement P d z.1, z.2), by fun_prop⟩
  at_zero _ := rfl
  at_one _ := rfl
  left _ := rfl
  right r := CutOpenCarrier.cylinderMinus_one (polyRef P d) (chart P d) (laurentRef P d) (ordinary
      P d) (shifted P d) (movement P d r)

/-- The original collapse and terminal-pause cancellation give this full carrier comparison. -/
def coneBoundaryMinus : (conePathMinus P d 0).Homotopy
    ((movementEdgeMinus P d).trans (conePathMinus P d 1)) :=
  (coneSquareMinus P d).coneBoundary

/-- Every native level of the entire actual square is the original interchange. -/
theorem squareMinus_native (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d) (ordinary P d) (shifted P
      d) n
      ((coneSquareMinus P d).parameter (r, s)) x = (nativeSquare P d n x).parameter (r, s) := by
  change CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d) (ordinary P d)
      (shifted P d) n
    (CutOpenCarrier.cylinderMinus (polyRef P d) (chart P d) (laurentRef P d) (ordinary P d)
      (shifted P d) (movement P d r, s)) x = _
  rw [CutOpenCarrier.nativeEval_cylinderMinus,
    CoefficientBassPositiveJ0PolynomialMovement.movement_native]
  rfl

/-- Evaluation preserves the full collapse and cancellation at both independent times. -/
theorem coneBoundaryMinus_native (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d) (ordinary P d) (shifted P
      d) n
      (coneBoundaryMinus P d (r, s)) x = (nativeSquare P d n x).coneBoundary (r, s) :=
  (coneSquareMinus P d).coneBoundary_natural (nativeSquare P d n x)
    (fun y ↦ CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d) (ordinary P d)
      (shifted P d) n y x)
    (fun r s ↦ squareMinus_native P d n r s x) r s

/-- The entire plus cylinder over one polynomial input, with its own actual tip. -/
def conePathPlus (r : I) : Path
    (CutOpenCarrier.cylinderPlus (polyRef P d) (chart P d) (laurentRef P d) (ordinary P d)
      (shifted P d) (movement P d r, 0))
    (CutOpenCarrier.tipPlus (polyRef P d) (chart P d) (laurentRef P d) (ordinary P d) (shifted P
      d)) where
  toFun s := CutOpenCarrier.cylinderPlus (polyRef P d) (chart P d) (laurentRef P d) (ordinary P d)
      (shifted P d) (movement P d r, s)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := CutOpenCarrier.cylinderPlus_one (polyRef P d) (chart P d) (laurentRef P d) (ordinary
      P d) (shifted P d) (movement P d r)

/-- The complete attached polynomial edge, with unchanged original movement time. -/
def movementEdgePlus : Path
    (CutOpenCarrier.cylinderPlus (polyRef P d) (chart P d) (laurentRef P d) (ordinary P d)
      (shifted P d) (movement P d 0, 0))
    (CutOpenCarrier.cylinderPlus (polyRef P d) (chart P d) (laurentRef P d) (ordinary P d)
      (shifted P d) (movement P d 1, 0)) where
  toFun r := CutOpenCarrier.cylinderPlus (polyRef P d) (chart P d) (laurentRef P d) (ordinary P d)
      (shifted P d) (movement P d r, 0)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

/-- The actual plus cone square, with all four original whole edges. -/
def coneSquarePlus : CarrierPathSquare.Square
    (conePathPlus P d 0) (conePathPlus P d 1) (movementEdgePlus P d)
    (Path.refl (CutOpenCarrier.tipPlus (polyRef P d) (chart P d) (laurentRef P d) (ordinary P d)
      (shifted P d))) where
  parameter := ⟨fun z ↦ CutOpenCarrier.cylinderPlus (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d)
    (movement P d z.1, z.2), by fun_prop⟩
  at_zero _ := rfl
  at_one _ := rfl
  left _ := rfl
  right r := CutOpenCarrier.cylinderPlus_one (polyRef P d) (chart P d) (laurentRef P d) (ordinary
      P d) (shifted P d) (movement P d r)

/-- The original collapse and terminal-pause cancellation give this full carrier comparison. -/
def coneBoundaryPlus : (conePathPlus P d 0).Homotopy
    ((movementEdgePlus P d).trans (conePathPlus P d 1)) :=
  (coneSquarePlus P d).coneBoundary

/-- Every native level of the entire actual square is the original interchange. -/
theorem squarePlus_native (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d) (ordinary P d) (shifted P
      d) n
      ((coneSquarePlus P d).parameter (r, s)) x = (nativeSquare P d n x).parameter (r, s) := by
  change CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d) (ordinary P d)
      (shifted P d) n
    (CutOpenCarrier.cylinderPlus (polyRef P d) (chart P d) (laurentRef P d) (ordinary P d)
      (shifted P d) (movement P d r, s)) x = _
  rw [CutOpenCarrier.nativeEval_cylinderPlus,
    CoefficientBassPositiveJ0PolynomialMovement.movement_native]
  rfl

/-- Evaluation preserves the full collapse and cancellation at both independent times. -/
theorem coneBoundaryPlus_native (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d) (ordinary P d) (shifted P
      d) n
      (coneBoundaryPlus P d (r, s)) x = (nativeSquare P d n x).coneBoundary (r, s) :=
  (coneSquarePlus P d).coneBoundary_natural (nativeSquare P d n x)
    (fun y ↦ CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d) (ordinary P d)
      (shifted P d) n y x)
    (fun r s ↦ squarePlus_native P d n r s x) r s

/-- The two complete constructions retain separate carrier tips throughout. -/
theorem tips_distinct :
    CutOpenCarrier.tipMinus (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) ≠
    CutOpenCarrier.tipPlus (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) :=
  CutOpenCarrier.tips_ne _ _ _ _ _

end Quillen.PerfectComplexes.CoefficientBassPositiveJ0ConeBoundaries
