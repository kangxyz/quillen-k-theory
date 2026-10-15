/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BoundedFlatBassNullSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BoundedFlatLaurentUnitSquareHomotopy
public import Quillen.Topology.Prespectrum.RelativeHomotopyConjugation
public import Quillen.Topology.Prespectrum.RelativeHomotopyLoop

/-!
# Actual coefficient naturality of the bounded-flat Bass transition

The proved original unit and nullhomotopy comparisons give a whole prespectrum homotopy between
the two literal transition composites. Higher composition coherence and closed iteration remain
separate requirements.
-/
@[expose] public section

open Quillen.PolynomialBaseChange

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes
namespace BassTransitionTrack
variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- The original old unit loop after Laurent coefficient change and target cone inclusion. -/
def oldUnit := (LaurentUnitTrack.oldUnit f).postcomp
  (mappingConeInclusion (boundedFlatBassSquareComparison S))

/-- The original new unit loop after base coefficient change and target cone inclusion. -/
def newUnit := (LaurentUnitTrack.newUnit f).postcomp
  (mappingConeInclusion (boundedFlatBassSquareComparison S))

/-- The proved unit pasting retains every original coordinate after target cone inclusion. -/
def unitPasting :
    ((oldUnit f).trans (BassNullTrack.laurentMovement f)).RelHomotopy
      ((BassNullTrack.laurentMovement f).trans (newUnit f)) := by
  simpa only [Homotopy.postcomp_trans, oldUnit, newUnit, BassNullTrack.laurentMovement] using
    (boundedFlatLaurentUnitCoefficientPasting f).postcomp
      (mappingConeInclusion (boundedFlatBassSquareComparison S))

/-- Cancel the proved actual moving Laurent track inside the two original null-loop conjugates. -/
def conjugateComparison :=
  Homotopy.RelHomotopy.conjugateNaturality (BassNullTrack.laurentMovement f)
    (oldUnit f) (newUnit f) (BassNullTrack.originalOldNull f) (BassNullTrack.originalNewNull f)
    (unitPasting f) (BassNullTrack.originalNullComparison f)

/-- The source based-loop map is the literal original transition followed by the actual step map. -/
lemma source_eq :
    ((oldUnit f).conjugateToZero (BassNullTrack.originalOldNull f)).zeroLoopMap =
      boundedFlatAffineBassTransition R ≫ boundedFlatAffineBassStepMap f := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Path.ext
  funext s
  change ((oldUnit f).conjugateToZero (BassNullTrack.originalOldNull f)).level n (s, x) =
    ((((boundedFlatLaurentUnitHomotopy R).postcomp
      (mappingConeInclusion (boundedFlatBassSquareComparison R))).conjugateToZero
        (boundedFlatBassLaurentNullHomotopy R)).postcomp (boundedFlatBassConeMap f)).level n (s, x)
  simp only [Homotopy.conjugateToZero, Homotopy.postcomp_trans, Homotopy.postcomp_symm]
  rfl

/-- The target based-loop map is the literal base coefficient map followed by the new transition. -/
lemma target_eq :
    ((newUnit f).conjugateToZero (BassNullTrack.originalNewNull f)).zeroLoopMap =
      boundedFlatPerfectPrespectrumMap (Spec.map f) ≫ boundedFlatAffineBassTransition S := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Path.ext
  funext s
  change ((newUnit f).conjugateToZero (BassNullTrack.originalNewNull f)).level n (s, x) =
    (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (Spec.map f))
      (((boundedFlatLaurentUnitHomotopy S).postcomp
        (mappingConeInclusion (boundedFlatBassSquareComparison S))).conjugateToZero
          (boundedFlatBassLaurentNullHomotopy S))).level n (s, x)
  simp only [Homotopy.conjugateToZero, Homotopy.precomp_trans, Homotopy.precomp_symm]
  rfl

end BassTransitionTrack
variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- Every coefficient map gives a genuine whole homotopy of the original Bass transitions. -/
def boundedFlatAffineBassTransitionCoefficientHomotopy :
    Homotopy (boundedFlatAffineBassTransition R ≫ boundedFlatAffineBassStepMap f)
      (boundedFlatPerfectPrespectrumMap (Spec.map f) ≫ boundedFlatAffineBassTransition S) :=
  (BassTransitionTrack.conjugateComparison f).zeroLoopMapHomotopy.cast
    (BassTransitionTrack.source_eq f) (BassTransitionTrack.target_eq f)

/-- The transition comparison retains the complete original relative conjugation track. -/
lemma boundedFlatAffineBassTransitionCoefficientHomotopy_apply (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space n) :
    Path.toContinuousMap
      ((boundedFlatAffineBassTransitionCoefficientHomotopy f).level n (r, x)) s =
        (BassTransitionTrack.conjugateComparison f).level n (r, (s, x)) := rfl

end Quillen.PerfectComplexes
