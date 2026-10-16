/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassNullTrack
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientLaurentUnitTrack
public import Quillen.Topology.Prespectrum.RelativeHomotopyConjugation
public import Quillen.Topology.Prespectrum.RelativeHomotopyLoop

/-!
# Actual native coefficient naturality of the original initial Bass seed

The produced original unit and positive-null comparisons give a whole prespectrum homotopy
between the two literal transition composites on arbitrary native coefficient fibers. The
comparison, output-loop and structure times remain independent. This constructs only the
initial seed naturality: the next Bass transition, higher fixed-composition compatibility
and mixed evaluation squares remain separate requirements.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes
namespace CoefficientBassTransitionTrack
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (u : a ⟶ b)

/-- The original old unit loop after Laurent coefficient change and target cone inclusion. -/
def oldUnit := (CoefficientLaurentUnitTrack.oldUnit P u).postcomp
  (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P b))

/-- The original new unit loop after base coefficient change and target cone inclusion. -/
def newUnit := (CoefficientLaurentUnitTrack.newUnit P u).postcomp
  (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P b))

/-- The proved unit pasting retains every original coordinate after target cone inclusion. -/
def unitPasting :
    ((oldUnit P u).trans (CoefficientBassNullTrack.laurentMovement P u)).RelHomotopy
      ((CoefficientBassNullTrack.laurentMovement P u).trans (newUnit P u)) := by
  simpa only [Homotopy.postcomp_trans, oldUnit, newUnit,
    CoefficientBassNullTrack.laurentMovement] using
    (boundedFlatCoefficientLaurentUnitPasting P u).postcomp
      (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P b))

/-- Cancel the proved actual moving Laurent track inside the two original null-loop conjugates. -/
def conjugateComparison :=
  Homotopy.RelHomotopy.conjugateNaturality (CoefficientBassNullTrack.laurentMovement P u)
    (oldUnit P u) (newUnit P u) (CoefficientBassNullTrack.originalOldNull P u)
    (CoefficientBassNullTrack.originalNewNull P u)
    (unitPasting P u) (CoefficientBassNullTrack.originalNullComparison P u)

/-- The source based-loop map is the literal original transition followed by the actual step map. -/
lemma source_eq :
    ((oldUnit P u).conjugateToZero (CoefficientBassNullTrack.originalOldNull P u)).zeroLoopMap =
      boundedFlatCoefficientBassTransition P a ≫ boundedFlatCoefficientBassStepMap P u := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Path.ext
  funext s
  change ((oldUnit P u).conjugateToZero
    (CoefficientBassNullTrack.originalOldNull P u)).level n (s, x) =
    ((((boundedFlatCoefficientLaurentUnitHomotopy P a).postcomp
      (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))).conjugateToZero
        (boundedFlatCoefficientBassLaurentNullHomotopy P a)).postcomp
          (boundedFlatCoefficientBassConeMap P u)).level n (s, x)
  simp only [Homotopy.conjugateToZero, Homotopy.postcomp_trans, Homotopy.postcomp_symm]
  rfl

/-- The target based-loop map is the literal base coefficient map followed by the new transition. -/
lemma target_eq :
    ((newUnit P u).conjugateToZero (CoefficientBassNullTrack.originalNewNull P u)).zeroLoopMap =
      boundedFlatPerfectPrespectrumMap (coefficientMap P u) ≫
        boundedFlatCoefficientBassTransition P b := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Path.ext
  funext s
  change ((newUnit P u).conjugateToZero
    (CoefficientBassNullTrack.originalNewNull P u)).level n (s, x) =
    (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (coefficientMap P u))
      (((boundedFlatCoefficientLaurentUnitHomotopy P b).postcomp
        (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P b))).conjugateToZero
          (boundedFlatCoefficientBassLaurentNullHomotopy P b))).level n (s, x)
  simp only [Homotopy.conjugateToZero, Homotopy.precomp_trans, Homotopy.precomp_symm]
  rfl

end CoefficientBassTransitionTrack
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (u : a ⟶ b)

/-- Every native coefficient map gives a genuine whole homotopy of the original Bass transitions. -/
def boundedFlatCoefficientBassTransitionCoefficientHomotopy :
    Homotopy (boundedFlatCoefficientBassTransition P a ≫ boundedFlatCoefficientBassStepMap P u)
      (boundedFlatPerfectPrespectrumMap (coefficientMap P u) ≫
        boundedFlatCoefficientBassTransition P b) :=
  (CoefficientBassTransitionTrack.conjugateComparison P u).zeroLoopMapHomotopy.cast
    (CoefficientBassTransitionTrack.source_eq P u) (CoefficientBassTransitionTrack.target_eq P u)

/-- The transition comparison retains the complete original relative conjugation track. -/
lemma boundedFlatCoefficientBassTransitionCoefficientHomotopy_apply (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    Path.toContinuousMap
      ((boundedFlatCoefficientBassTransitionCoefficientHomotopy P u).level n (r, x)) s =
        (CoefficientBassTransitionTrack.conjugateComparison P u).level n (r, (s, x)) := rfl

end Quillen.PerfectComplexes
