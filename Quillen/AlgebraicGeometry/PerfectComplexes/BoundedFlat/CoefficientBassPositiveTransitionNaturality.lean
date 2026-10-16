/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveNullTrack
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassTransitionNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientLaurentUnitTrack
public import Quillen.Topology.Prespectrum.RelativeHomotopyPostcompConjugation
public import Quillen.Topology.Prespectrum.RelativeHomotopyLoop

/-!
# Exact positive-support factor of the chosen initial-seed coefficient homotopy

The original unit/null recipe is performed in the positive cone, retaining its original
geometric pastings, associators, cancellations and independent parameters. Its whole image
under the strict positive inclusion is the already chosen initial-seed coefficient homotopy.
The higher mixed C0/J0/C1 projection pasting remains a separate obligation.
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
namespace CoefficientBassPositiveTransitionTrack
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (u : a ⟶ b)

/-- The original old unit loop after Laurent coefficient change and target cone inclusion. -/
def oldUnit := (CoefficientLaurentUnitTrack.oldUnit P u).postcomp
  (mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P b)))

/-- The original new unit loop after base coefficient change and target cone inclusion. -/
def newUnit := (CoefficientLaurentUnitTrack.newUnit P u).postcomp
  (mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P b)))

/-- The proved unit pasting retains every original coordinate after target cone inclusion. -/
def unitPasting :
    ((oldUnit P u).trans (CoefficientBassPositiveNullTrack.laurentMovement P u)).RelHomotopy
      ((CoefficientBassPositiveNullTrack.laurentMovement P u).trans (newUnit P u)) := by
  simpa only [Homotopy.postcomp_trans, oldUnit, newUnit,
    CoefficientBassPositiveNullTrack.laurentMovement] using
    (boundedFlatCoefficientLaurentUnitPasting P u).postcomp
      (mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P b)))

/-- Cancel the proved actual moving Laurent track inside the two original null-loop conjugates. -/
def conjugateComparison :=
  Homotopy.RelHomotopy.conjugateNaturality (CoefficientBassPositiveNullTrack.laurentMovement P u)
    (oldUnit P u) (newUnit P u) (CoefficientBassPositiveNullTrack.originalOldNull P u)
    (CoefficientBassPositiveNullTrack.originalNewNull P u)
    (unitPasting P u) (CoefficientBassPositiveNullTrack.originalNullComparison P u)

/-- The source based-loop map is the literal original transition followed by the actual step map. -/
lemma source_eq :
    ((oldUnit P u).conjugateToZero
      (CoefficientBassPositiveNullTrack.originalOldNull P u)).zeroLoopMap =
      boundedFlatCoefficientBassPositiveConeSeed P a ≫
        parameterLoopingMap (boundedFlatCoefficientBassPositiveConeMap P u) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Path.ext
  funext s
  change ((oldUnit P u).conjugateToZero
    (CoefficientBassPositiveNullTrack.originalOldNull P u)).level n (s, x) =
    ((((boundedFlatCoefficientLaurentUnitHomotopy P a).postcomp
      (mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P a)))).conjugateToZero
        (boundedFlatCoefficientBassPositiveConeNull P a)).postcomp
          (boundedFlatCoefficientBassPositiveConeMap P u)).level n (s, x)
  simp only [Homotopy.conjugateToZero, Homotopy.postcomp_trans, Homotopy.postcomp_symm]
  rfl

/-- The target based-loop map is the literal base coefficient map followed by the new transition. -/
lemma target_eq :
    ((newUnit P u).conjugateToZero
      (CoefficientBassPositiveNullTrack.originalNewNull P u)).zeroLoopMap =
      boundedFlatPerfectPrespectrumMap (coefficientMap P u) ≫
        boundedFlatCoefficientBassPositiveConeSeed P b := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Path.ext
  funext s
  change ((newUnit P u).conjugateToZero
    (CoefficientBassPositiveNullTrack.originalNewNull P u)).level n (s, x) =
    (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (coefficientMap P u))
      (((boundedFlatCoefficientLaurentUnitHomotopy P b).postcomp
        (mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P b)))).conjugateToZero
          (boundedFlatCoefficientBassPositiveConeNull P b))).level n (s, x)
  simp only [Homotopy.conjugateToZero, Homotopy.precomp_trans, Homotopy.precomp_symm]
  rfl

end CoefficientBassPositiveTransitionTrack
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (u : a ⟶ b)

/-- Every native coefficient map gives a genuine whole homotopy of the original Bass transitions. -/
def boundedFlatCoefficientBassPositiveTransitionHomotopy :
    Homotopy (boundedFlatCoefficientBassPositiveConeSeed P a ≫
      parameterLoopingMap (boundedFlatCoefficientBassPositiveConeMap P u))
      (boundedFlatPerfectPrespectrumMap (coefficientMap P u) ≫
        boundedFlatCoefficientBassPositiveConeSeed P b) :=
  (CoefficientBassPositiveTransitionTrack.conjugateComparison P u).zeroLoopMapHomotopy.cast
    (CoefficientBassPositiveTransitionTrack.source_eq P u)
    (CoefficientBassPositiveTransitionTrack.target_eq P u)

/-- The transition comparison retains the complete original relative conjugation track. -/
lemma boundedFlatCoefficientBassPositiveTransitionHomotopy_apply (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    Path.toContinuousMap
      ((boundedFlatCoefficientBassPositiveTransitionHomotopy P u).level n (r, x)) s =
        (CoefficientBassPositiveTransitionTrack.conjugateComparison P u).level n (r, (s, x)) := rfl


namespace CoefficientBassPositiveTransitionTrack

/-- Every coordinate of the actual old unit loop has its original full-cone image. -/
theorem oldUnit_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (oldUnit P u).MappedAt (boundedFlatCoefficientBassPositiveConeInclusion P b) n x
      (CoefficientBassTransitionTrack.oldUnit P u) := by
  intro s
  rfl

/-- Every coordinate of the actual new unit loop has its original full-cone image. -/
theorem newUnit_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (newUnit P u).MappedAt (boundedFlatCoefficientBassPositiveConeInclusion P b) n x
      (CoefficientBassTransitionTrack.newUnit P u) := by
  intro s
  rfl

/-- The original supplied unit intertwining retains all its comparison and path times. -/
theorem unitPasting_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (unitPasting P u).MappedAt (boundedFlatCoefficientBassPositiveConeInclusion P b) n x
      (CoefficientBassTransitionTrack.unitPasting P u) := by
  unfold unitPasting CoefficientBassTransitionTrack.unitPasting
  apply Homotopy.RelHomotopy.MappedAt.transport
  all_goals try simp only [Homotopy.postcomp_trans, oldUnit, newUnit,
    CoefficientBassPositiveNullTrack.laurentMovement, CoefficientBassTransitionTrack.oldUnit,
    CoefficientBassTransitionTrack.newUnit, CoefficientBassNullTrack.laurentMovement]
  intro r s
  rfl

/-- The unchanged old null after gamma retains the complete original mapped-null route. -/
theorem originalOldNull_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (CoefficientBassPositiveNullTrack.originalOldNull P u).MappedAt
      (boundedFlatCoefficientBassPositiveConeInclusion P b) n x
      (CoefficientBassNullTrack.originalOldNull P u) := by
  intro s
  rw [CoefficientBassPositiveNullTrack.originalOldNull_level,
    CoefficientBassNullTrack.originalOldNull_level]
  exact ((CoefficientBassPositiveNullTrack.oldPositive_mapped P u n x).trans
    ((CoefficientBassPositiveNullTrack.positiveMovement_mapped P u n x).trans
      (CoefficientBassPositiveNullTrack.oldCone_mapped P u n x))) s

/-- The unchanged new null retains the complete original precomposed-null route. -/
theorem originalNewNull_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (CoefficientBassPositiveNullTrack.originalNewNull P u).MappedAt
      (boundedFlatCoefficientBassPositiveConeInclusion P b) n x
      (CoefficientBassNullTrack.originalNewNull P u) := by
  intro s
  rw [CoefficientBassPositiveNullTrack.originalNewNull_level,
    CoefficientBassNullTrack.originalNewNull_level]
  exact ((CoefficientBassPositiveNullTrack.newPositive_mapped P u n x).trans
    (CoefficientBassPositiveNullTrack.newCone_mapped P u n x)) s

/-- The entire chosen relative conjugation is the image of the identical positive-cone recipe. -/
theorem conjugateComparison_mapped (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (conjugateComparison P u).MappedAt (boundedFlatCoefficientBassPositiveConeInclusion P b) n x
      (CoefficientBassTransitionTrack.conjugateComparison P u) := by
  apply Homotopy.RelHomotopy.conjugateNaturality_mapped
  · exact CoefficientBassPositiveNullTrack.laurentMovement_mapped P u n x
  · exact oldUnit_mapped P u n x
  · exact newUnit_mapped P u n x
  · exact originalNewNull_mapped P u n x
  · exact unitPasting_mapped P u n x
  · exact CoefficientBassPositiveNullTrack.originalNullComparison_mapped P u n x

end CoefficientBassPositiveTransitionTrack

/-- The whole existing chosen J0 is recovered at every original degree, comparison time,
output-loop time and source point, using the identical original unit/null recipe. -/
theorem boundedFlatCoefficientBassPositiveTransitionHomotopy_factor
    (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (boundedFlatCoefficientBassPositiveConeInclusion P b).map n
      (Path.toContinuousMap
        ((boundedFlatCoefficientBassPositiveTransitionHomotopy P u).level n (r, x)) s) =
    Path.toContinuousMap
      ((boundedFlatCoefficientBassTransitionCoefficientHomotopy P u).level n (r, x)) s :=
  CoefficientBassPositiveTransitionTrack.conjugateComparison_mapped P u n x r s

end Quillen.PerfectComplexes
