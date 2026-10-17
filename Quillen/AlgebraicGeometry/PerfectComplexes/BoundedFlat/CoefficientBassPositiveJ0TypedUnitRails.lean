/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Aglib.Topology.Path.RetypedUnitComparison
public import Quillen.Topology.Prespectrum.RelativeHomotopyFactorEvaluation
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveJ0UnitPasting
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveJ0FullNullNative

/-! Actual unit endpoints and all eight whole path-image roles for two-sheet conjugation. -/
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
namespace Quillen.PerfectComplexes.CoefficientBassPositiveJ0TypedUnitRails
open CommonReferenceNerve CoefficientBassPositiveJ0ConeBoundaries
open CoefficientBassPositiveJ0Rectangles CoefficientBassPositiveJ0PairedNull
open CoefficientBassPositiveJ0PairedNullNative CoefficientBassPositiveJ0PositiveRailsNative
private theorem carrier_path_apply {X : Type u} [TopologicalSpace X] {a b : X}
    (p : Path a b) (s : I) : p.toContinuousMap s = p s := rfl

private theorem native_path_apply {E F : LoopPrespectrum.{u}} {f g : E ⟶ F}
    (H : LoopPrespectrum.Homotopy f g) (n : ℕ) (x : E.space n) (s : I) :
    H.path n x s = H.level n (s, x) := rfl

variable {R : CommRingCat.{u}} (P : Over (Spec R)) (d : Under R)

/-- The old unit joins the two actual old-null sources, without identifying them. -/
abbrev oldUnit := Path.RetypedUnitComparison.oldUnit
  (CoefficientBassPositiveJ0UnitPasting.oldUnit P d)
  (CoefficientBassPositiveJ0UnitPasting.lower P d)
  (CoefficientBassPositiveJ0UnitPasting.upper P d)
  (laurentMovementMinus P d) (laurentMovementPlus P d)
  (CoefficientBassPositiveJ0UnitPasting.lower_rail P d)
  (CoefficientBassPositiveJ0UnitPasting.upper_rail P d)

/-- The new unit joins the two actual new-null sources, retaining both sheets. -/
abbrev newUnit := Path.RetypedUnitComparison.newUnit
  (CoefficientBassPositiveJ0UnitPasting.newUnit P d)
  (CoefficientBassPositiveJ0UnitPasting.lower P d)
  (CoefficientBassPositiveJ0UnitPasting.upper P d)
  (laurentMovementMinus P d) (laurentMovementPlus P d)
  (CoefficientBassPositiveJ0UnitPasting.lower_rail P d)
  (CoefficientBassPositiveJ0UnitPasting.upper_rail P d)

/-- The complete original unit comparison uses exactly the two selected Laurent rails. -/
def unitComparison : ((oldUnit P d).trans (laurentMovementPlus P d)).Homotopy
    ((laurentMovementMinus P d).trans (newUnit P d)) :=
  Path.RetypedUnitComparison.comparison
    (CoefficientBassPositiveJ0UnitPasting.oldUnit P d)
    (CoefficientBassPositiveJ0UnitPasting.newUnit P d)
    (CoefficientBassPositiveJ0UnitPasting.lower P d)
    (CoefficientBassPositiveJ0UnitPasting.upper P d)
    (laurentMovementMinus P d) (laurentMovementPlus P d)
    (CoefficientBassPositiveJ0UnitPasting.lower_rail P d)
    (CoefficientBassPositiveJ0UnitPasting.upper_rail P d)
    (CoefficientBassPositiveJ0UnitPasting.unitComparison P d)

/-- The full comparison has the unchanged original native image. -/
theorem unitComparison_native (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (unitComparison P d (r, s)) x =
      (CoefficientBassPositiveTransitionTrack.unitPasting P (arrow d)).level n (r, (s, x)) :=
  CoefficientBassPositiveJ0UnitPasting.native P d n r s x

/-- The whole oldUnit native image follows from the actual unit comparison boundary. -/
theorem oldUnit_native (n : ℕ) (s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (oldUnit P d s) x =
      (CoefficientBassPositiveTransitionTrack.oldUnit P (arrow d)).level n (s, x) := by
  let E := originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, d)))
  let F := LoopPrespectrum.mappingCone
    (boundedFlatPerfectPrespectrumMap (laurentPlus P ((laurentUnderFunctor R).obj d)))
  let ev : Carrier P d → F.space n := fun z ↦
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n z x
  exact NativeFactorEvaluation.comparison_source_left (E := E) (F := F) n x ev
    (oldUnit P d) (laurentMovementPlus P d)
    ((laurentMovementMinus P d).trans (newUnit P d))
    (CoefficientBassPositiveTransitionTrack.oldUnit P (arrow d))
    (CoefficientBassPositiveNullTrack.laurentMovement P (arrow d))
    ((CoefficientBassPositiveNullTrack.laurentMovement P (arrow d)).trans
      (CoefficientBassPositiveTransitionTrack.newUnit P (arrow d)))
    (unitComparison P d) (CoefficientBassPositiveTransitionTrack.unitPasting P (arrow d))
    (fun r t ↦ unitComparison_native P d n r t x) s

/-- The whole newUnit native image follows from the actual unit comparison boundary. -/
theorem newUnit_native (n : ℕ) (s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (newUnit P d s) x =
      (CoefficientBassPositiveTransitionTrack.newUnit P (arrow d)).level n (s, x) := by
  let E := originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, d)))
  let F := LoopPrespectrum.mappingCone
    (boundedFlatPerfectPrespectrumMap (laurentPlus P ((laurentUnderFunctor R).obj d)))
  let ev : Carrier P d → F.space n := fun z ↦
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n z x
  exact NativeFactorEvaluation.comparison_target_right (E := E) (F := F) n x ev
    (laurentMovementMinus P d) (newUnit P d)
    ((oldUnit P d).trans (laurentMovementPlus P d))
    (CoefficientBassPositiveNullTrack.laurentMovement P (arrow d))
    (CoefficientBassPositiveTransitionTrack.newUnit P (arrow d))
    ((CoefficientBassPositiveTransitionTrack.oldUnit P (arrow d)).trans
      (CoefficientBassPositiveNullTrack.laurentMovement P (arrow d)))
    (unitComparison P d) (CoefficientBassPositiveTransitionTrack.unitPasting P (arrow d))
    (fun r t ↦ unitComparison_native P d n r t x) s

private theorem trans_native {X : Type u} [TopologicalSpace X] {a b c : X}
    {E F : LoopPrespectrum.{u}} {f g k : E ⟶ F}
    (n : ℕ) (x : E.space n) (ev : X → F.space n)
    (p : Path a b) (q : Path b c)
    (H : LoopPrespectrum.Homotopy f g) (K : LoopPrespectrum.Homotopy g k)
    (hp : ∀ s, ev (p s) = H.level n (s, x))
    (hq : ∀ s, ev (q s) = K.level n (s, x)) (s : I) :
    ev ((p.trans q) s) = (H.trans K).level n (s, x) := by
  change ev ((p.trans q) s) = (H.trans K).path n x s
  rw [LoopPrespectrum.Homotopy.path_trans]
  exact Path.Evaluation.path_trans ev p q (H.path n x) (K.path n x) hp hq s

/-- The minus movement whole image retains its own carrier endpoints. -/
theorem movementMinus_native (n : ℕ) (s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (laurentMovementMinus P d s) x =
      (CoefficientBassPositiveNullTrack.laurentMovement P (arrow d)).level n (s, x) := by
  exact laurentMovementMinus_native P d n s x

/-- The minus oldNull whole image retains its own carrier endpoints. -/
theorem oldNullMinus_native (n : ℕ) (s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (oldNullMinus P d s) x =
      (CoefficientBassPositiveNullTrack.originalOldNull P (arrow d)).level n (s, x) := by
  rw [CoefficientBassPositiveNullTrack.originalOldNull_level]
  let ev := fun z : Carrier P d ↦
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n z x
  exact trans_native n x ev _ _ _ _
    (fun t ↦ oldPositiveMinus_native P d n t x)
    (trans_native n x ev _ _ _ _
      (fun t ↦ positiveMovementMinus_native P d n t x)
      (fun t ↦ oldConeMinus_native P d n t x)) s

/-- The minus newNull whole image retains its own carrier endpoints. -/
theorem newNullMinus_native (n : ℕ) (s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (newNullMinus P d s) x =
      (CoefficientBassPositiveNullTrack.originalNewNull P (arrow d)).level n (s, x) := by
  rw [CoefficientBassPositiveNullTrack.originalNewNull_level]
  let ev := fun z : Carrier P d ↦
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n z x
  exact trans_native n x ev _ _ _ _
    (fun t ↦ newPositiveMinus_native P d n t x)
    (fun t ↦ newConeMinus_native P d n t x) s

/-- The plus movement whole image retains its own carrier endpoints. -/
theorem movementPlus_native (n : ℕ) (s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (laurentMovementPlus P d s) x =
      (CoefficientBassPositiveNullTrack.laurentMovement P (arrow d)).level n (s, x) := by
  exact laurentMovementPlus_native P d n s x

/-- The plus oldNull whole image retains its own carrier endpoints. -/
theorem oldNullPlus_native (n : ℕ) (s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (oldNullPlus P d s) x =
      (CoefficientBassPositiveNullTrack.originalOldNull P (arrow d)).level n (s, x) := by
  rw [CoefficientBassPositiveNullTrack.originalOldNull_level]
  let ev := fun z : Carrier P d ↦
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n z x
  exact trans_native n x ev _ _ _ _
    (fun t ↦ oldPositivePlus_native P d n t x)
    (trans_native n x ev _ _ _ _
      (fun t ↦ positiveMovementPlus_native P d n t x)
      (fun t ↦ oldConePlus_native P d n t x)) s

/-- The plus newNull whole image retains its own carrier endpoints. -/
theorem newNullPlus_native (n : ℕ) (s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (newNullPlus P d s) x =
      (CoefficientBassPositiveNullTrack.originalNewNull P (arrow d)).level n (s, x) := by
  rw [CoefficientBassPositiveNullTrack.originalNewNull_level]
  let ev := fun z : Carrier P d ↦
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n z x
  exact trans_native n x ev _ _ _ _
    (fun t ↦ newPositivePlus_native P d n t x)
    (fun t ↦ newConePlus_native P d n t x) s

end Quillen.PerfectComplexes.CoefficientBassPositiveJ0TypedUnitRails
