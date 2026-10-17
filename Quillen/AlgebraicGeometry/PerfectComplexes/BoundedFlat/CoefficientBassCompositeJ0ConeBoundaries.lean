/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeJ0ShiftedPolynomial
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveNullTrack
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
namespace Quillen.PerfectComplexes.CoefficientBassCompositeJ0ConeBoundaries
open CommonReferenceNerve CoefficientBassPositiveC1BoundaryLift
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)
/-- The same chosen polynomial reference used by the actual carrier. -/
abbrev polyRef := CoefficientBassCompositeJ0Polynomial.reference P p q
/-- The same chosen common Laurent reference. -/
abbrev laurentRef := laurentReference P p q
/-- The original target positive chart model map. -/
abbrev chart := chartMap P (c := c)
/-- The actual ordinary attachment isomorphism. -/
abbrev ordinary := ordinaryAnchor P p q
/-- The actual forward-unit shifted attachment isomorphism. -/
abbrev shifted :=
  LaurentUnitReferenceSpecialization.shiftedAnchor P p q
/-- The entire original polynomial movement with its unchanged clock. -/
abbrev movement := CoefficientBassCompositeJ0Polynomial.movement P p q
/-- The original direct Laurent coefficient arrow. -/
abbrev arrow := CoefficientBassCompositeJ0Polynomial.arrow p q
/-- The original full polynomial and mapping-cone interchange square. -/
abbrev nativeInterchange := LoopPrespectrum.Homotopy.Square.interchange
  (boundedFlatCoefficientPolynomialSquareHomotopy P (arrow p q))
  (LoopPrespectrum.mappingConeHomotopy (prespectrumMap (chart P (c := c))))

/-- The original old cone path at an arbitrary native level and source point. -/
abbrev nativeOld (n : ℕ)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :=
  (CoefficientBassPositiveNullTrack.oldCone P (arrow p q)).path n x

/-- The original new cone path, retaining its original endpoint casts. -/
abbrev nativeNew (n : ℕ)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :=
  (CoefficientBassPositiveNullTrack.newCone P (arrow p q)).path n x

/-- The original polynomial movement followed by chart and cone inclusion. -/
abbrev nativeMove (n : ℕ)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :=
  (CoefficientBassPositiveNullTrack.polynomialMovement P (arrow p q)).path n x

/-- The target square is the existing native interchange, evaluated at a fixed source point. -/
def nativeSquare (n : ℕ)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CarrierPathSquare.Square (nativeOld P p q n x) (nativeNew P p q n x)
      (nativeMove P p q n x) (Path.refl ((CutOpenCarrier.nativeCone (chart P (c := c))).point n))
        where
  parameter := ⟨fun z ↦ (nativeInterchange P p q).level n (z.1, (z.2, x)), by fun_prop⟩
  at_zero s := (nativeInterchange P p q).at_zero n s x
  at_one s := (nativeInterchange P p q).at_one n s x
  left r := (nativeInterchange P p q).left n r x
  right r := (nativeInterchange P p q).right n r x

/-- The entire minus cylinder over one polynomial input, with its own actual tip. -/
def conePathMinus (r : I) : Path
    (CutOpenCarrier.cylinderMinus (polyRef P p q) (chart P (c := c)) (laurentRef P p q) (ordinary
      P p q)
      (shifted P p q) (movement P p q r, 0))
    (CutOpenCarrier.tipMinus (polyRef P p q) (chart P (c := c)) (laurentRef P p q) (ordinary P p q)
      (shifted P p q)) where
  toFun s := CutOpenCarrier.cylinderMinus (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
    (ordinary P p q) (shifted P p q) (movement P p q r, s)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := CutOpenCarrier.cylinderMinus_one (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary
      P p q) (shifted P p q) (movement P p q r)

/-- The complete attached polynomial edge, with unchanged original movement time. -/
def movementEdgeMinus : Path
    (CutOpenCarrier.cylinderMinus (polyRef P p q) (chart P (c := c)) (laurentRef P p q) (ordinary
      P p q)
      (shifted P p q) (movement P p q 0, 0))
    (CutOpenCarrier.cylinderMinus (polyRef P p q) (chart P (c := c)) (laurentRef P p q) (ordinary
      P p q)
      (shifted P p q) (movement P p q 1, 0)) where
  toFun r := CutOpenCarrier.cylinderMinus (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
    (ordinary P p q) (shifted P p q) (movement P p q r, 0)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

/-- The actual minus cone square, with all four original whole edges. -/
def coneSquareMinus : CarrierPathSquare.Square
    (conePathMinus P p q 0) (conePathMinus P p q 1) (movementEdgeMinus P p q)
    (Path.refl (CutOpenCarrier.tipMinus (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q)
      (shifted P p q))) where
  parameter := ⟨fun z ↦ CutOpenCarrier.cylinderMinus (polyRef P p q) (chart P (c := c))
    (laurentRef P
      p q)
      (ordinary P p q) (shifted P p q)
    (movement P p q z.1, z.2), by fun_prop⟩
  at_zero _ := rfl
  at_one _ := rfl
  left _ := rfl
  right r := CutOpenCarrier.cylinderMinus_one (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary
      P p q) (shifted P p q) (movement P p q r)

/-- The original collapse and terminal-pause cancellation give this full carrier comparison. -/
def coneBoundaryMinus : (conePathMinus P p q 0).Homotopy
    ((movementEdgeMinus P p q).trans (conePathMinus P p q 1)) :=
  (coneSquareMinus P p q).coneBoundary

/-- Every native level of the entire actual square is the original interchange. -/
theorem squareMinus_native (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q) (ordinary P p q)
      (shifted P p q) n
      ((coneSquareMinus P p q).parameter (r, s)) x = (nativeSquare P p q n x).parameter (r, s) := by
  change CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
    (ordinary P p q)
      (shifted P p q) n
    (CutOpenCarrier.cylinderMinus (polyRef P p q) (chart P (c := c)) (laurentRef P p q) (ordinary
      P p q)
      (shifted P p q) (movement P p q r, s)) x = _
  rw [CutOpenCarrier.nativeEval_cylinderMinus,
    CoefficientBassCompositeJ0Polynomial.movement_native]
  rfl

/-- Evaluation preserves the full collapse and cancellation at both independent times. -/
theorem coneBoundaryMinus_native (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q) (ordinary P p q)
      (shifted P p q) n
      (coneBoundaryMinus P p q (r, s)) x = (nativeSquare P p q n x).coneBoundary (r, s) :=
  (coneSquareMinus P p q).coneBoundary_natural (nativeSquare P p q n x)
    (fun y ↦ CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary
      P p q)
      (shifted P p q) n y x)
    (fun r s ↦ squareMinus_native P p q n r s x) r s

/-- The entire plus cylinder over one polynomial input, with its own actual tip. -/
def conePathPlus (r : I) : Path
    (CutOpenCarrier.cylinderPlus (polyRef P p q) (chart P (c := c)) (laurentRef P p q) (ordinary
      P p q)
      (shifted P p q) (movement P p q r, 0))
    (CutOpenCarrier.tipPlus (polyRef P p q) (chart P (c := c)) (laurentRef P p q) (ordinary P p q)
      (shifted P p q)) where
  toFun s := CutOpenCarrier.cylinderPlus (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q)
      (shifted P p q) (movement P p q r, s)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := CutOpenCarrier.cylinderPlus_one (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary
      P p q) (shifted P p q) (movement P p q r)

/-- The complete attached polynomial edge, with unchanged original movement time. -/
def movementEdgePlus : Path
    (CutOpenCarrier.cylinderPlus (polyRef P p q) (chart P (c := c)) (laurentRef P p q) (ordinary
      P p q)
      (shifted P p q) (movement P p q 0, 0))
    (CutOpenCarrier.cylinderPlus (polyRef P p q) (chart P (c := c)) (laurentRef P p q) (ordinary
      P p q)
      (shifted P p q) (movement P p q 1, 0)) where
  toFun r := CutOpenCarrier.cylinderPlus (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q)
      (shifted P p q) (movement P p q r, 0)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

/-- The actual plus cone square, with all four original whole edges. -/
def coneSquarePlus : CarrierPathSquare.Square
    (conePathPlus P p q 0) (conePathPlus P p q 1) (movementEdgePlus P p q)
    (Path.refl (CutOpenCarrier.tipPlus (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary
      P p q)
      (shifted P p q))) where
  parameter := ⟨fun z ↦ CutOpenCarrier.cylinderPlus (polyRef P p q) (chart P (c := c))
    (laurentRef P p q)
      (ordinary P p q) (shifted P p q)
    (movement P p q z.1, z.2), by fun_prop⟩
  at_zero _ := rfl
  at_one _ := rfl
  left _ := rfl
  right r := CutOpenCarrier.cylinderPlus_one (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary
      P p q) (shifted P p q) (movement P p q r)

/-- The original collapse and terminal-pause cancellation give this full carrier comparison. -/
def coneBoundaryPlus : (conePathPlus P p q 0).Homotopy
    ((movementEdgePlus P p q).trans (conePathPlus P p q 1)) :=
  (coneSquarePlus P p q).coneBoundary

/-- Every native level of the entire actual square is the original interchange. -/
theorem squarePlus_native (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q) (ordinary P p q)
      (shifted P p q) n
      ((coneSquarePlus P p q).parameter (r, s)) x = (nativeSquare P p q n x).parameter (r, s) := by
  change CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
    (ordinary P p q)
      (shifted P p q) n
    (CutOpenCarrier.cylinderPlus (polyRef P p q) (chart P (c := c)) (laurentRef P p q) (ordinary
      P p q)
      (shifted P p q) (movement P p q r, s)) x = _
  rw [CutOpenCarrier.nativeEval_cylinderPlus,
    CoefficientBassCompositeJ0Polynomial.movement_native]
  rfl

/-- Evaluation preserves the full collapse and cancellation at both independent times. -/
theorem coneBoundaryPlus_native (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q) (ordinary P p q)
      (shifted P p q) n
      (coneBoundaryPlus P p q (r, s)) x = (nativeSquare P p q n x).coneBoundary (r, s) :=
  (coneSquarePlus P p q).coneBoundary_natural (nativeSquare P p q n x)
    (fun y ↦ CutOpenCarrier.nativeEval (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary
      P p q)
      (shifted P p q) n y x)
    (fun r s ↦ squarePlus_native P p q n r s x) r s

/-- The two complete constructions retain separate carrier tips throughout. -/
theorem tips_distinct :
    CutOpenCarrier.tipMinus (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) ≠
    CutOpenCarrier.tipPlus (polyRef P p q) (chart P (c := c)) (laurentRef P p q)
      (ordinary P p q) (shifted P p q) :=
  CutOpenCarrier.tips_ne _ _ _ _ _

end Quillen.PerfectComplexes.CoefficientBassCompositeJ0ConeBoundaries
