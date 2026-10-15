/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BassInclusionNullTrack
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.InclusionUnitTrack
public import Quillen.Topology.Prespectrum.RelativeHomotopyConjugation
public import Quillen.Topology.Prespectrum.RelativeHomotopyLoop

/-!
# The original geometric Bass comparison preserves the original transition

The genuine original Laurent-unit inclusion pasting and original Laurent-null comparison give a
whole homotopy between the two unchanged transition composites. Every based-loop parameter and
independent structure-map parameter is retained. No compatibility premise is supplied.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes
namespace BassInclusionTransitionTrack
variable (R : CommRingCat.{u})

/-- The original bounded-flat unit loop after Laurent inclusion and perfect cone inclusion. -/
def oldUnit :=
  ((boundedFlatLaurentUnitHomotopy R).postcomp (exactOriginalPrespectrumMap
    (boundedFlatPerfectWaldhausen (Spec (.of (LaurentPolynomial R))))
    (perfectWaldhausen (Spec (.of (LaurentPolynomial R))))
    (boundedFlatPerfectInclusion_exact _))).postcomp (mappingConeInclusion (bassSquareComparison R))

/-- The original perfect Laurent-unit loop after base inclusion and perfect cone inclusion. -/
def newUnit :=
  (Homotopy.precomp (exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen (Spec R))
    (perfectWaldhausen (Spec R)) (boundedFlatPerfectInclusion_exact _))
    (laurentUnitHomotopy R)).postcomp (mappingConeInclusion (bassSquareComparison R))

/-- The proved actual scalar inclusion identity supplies the entire original unit pasting. -/
def unitPasting :
    ((oldUnit R).trans (BassInclusionNullTrack.laurentMovement R)).RelHomotopy
      ((BassInclusionNullTrack.laurentMovement R).trans (newUnit R)) := by
  simpa only [Homotopy.postcomp_trans, oldUnit, newUnit, BassInclusionNullTrack.laurentMovement,
    boundedFlatLaurentUnitHomotopy, laurentUnitHomotopy] using
    (boundedFlatPerfectInclusionUnitTrack (laurentProjection R) (laurentGlobalUnit R)).postcomp
      (mappingConeInclusion (bassSquareComparison R))

/-- The proved unit and null comparisons identify the two actual original based conjugates. -/
def conjugateComparison :=
  Homotopy.RelHomotopy.conjugateNaturality (BassInclusionNullTrack.laurentMovement R)
    (oldUnit R) (newUnit R) (BassInclusionNullTrack.originalOldNull R)
    (BassInclusionNullTrack.originalNewNull R) (unitPasting R)
    (BassInclusionNullTrack.originalNullComparison R)

/-- The source loop map is exactly the old transition followed by the proved geometric Bass map. -/
theorem source_eq :
    ((oldUnit R).conjugateToZero (BassInclusionNullTrack.originalOldNull R)).zeroLoopMap =
      boundedFlatAffineBassTransition R ≫ boundedFlatPerfectGeometricBassStepMap R := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Path.ext
  funext s
  change ((oldUnit R).conjugateToZero (BassInclusionNullTrack.originalOldNull R)).level n (s, x) =
    ((((boundedFlatLaurentUnitHomotopy R).postcomp
      (mappingConeInclusion (boundedFlatBassSquareComparison R))).conjugateToZero
        (boundedFlatBassLaurentNullHomotopy R)).postcomp
          (boundedFlatPerfectGeometricBassConeMap R)).level n (s, x)
  simp only [Homotopy.conjugateToZero, Homotopy.postcomp_trans, Homotopy.postcomp_symm]
  rfl

/-- The target loop map is exactly original base inclusion followed by the perfect transition. -/
theorem target_eq :
    ((newUnit R).conjugateToZero (BassInclusionNullTrack.originalNewNull R)).zeroLoopMap =
      exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen (Spec R))
        (perfectWaldhausen (Spec R)) (boundedFlatPerfectInclusion_exact _) ≫
        affineBassTransition R := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Path.ext
  funext s
  change ((newUnit R).conjugateToZero (BassInclusionNullTrack.originalNewNull R)).level n (s, x) =
    (Homotopy.precomp (exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen (Spec R))
      (perfectWaldhausen (Spec R)) (boundedFlatPerfectInclusion_exact _))
      (((laurentUnitHomotopy R).postcomp
        (mappingConeInclusion (bassSquareComparison R))).conjugateToZero
          (bassLaurentNullHomotopy R))).level n (s, x)
  simp only [Homotopy.conjugateToZero, Homotopy.precomp_trans, Homotopy.precomp_symm]
  rfl

end BassInclusionTransitionTrack
variable (R : CommRingCat.{u})

/-- The actual geometric bounded-flat/perfect Bass step comparison preserves both original
transitions through a genuine whole-prespectrum homotopy, with no seed-compatibility premise. -/
def boundedFlatPerfectBassTransitionHomotopy :
    Homotopy (boundedFlatAffineBassTransition R ≫ boundedFlatPerfectGeometricBassStepMap R)
      (exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen (Spec R))
        (perfectWaldhausen (Spec R)) (boundedFlatPerfectInclusion_exact _) ≫
        affineBassTransition R) :=
  (BassInclusionTransitionTrack.conjugateComparison R).zeroLoopMapHomotopy.cast
    (BassInclusionTransitionTrack.source_eq R) (BassInclusionTransitionTrack.target_eq R)

/-- The transition comparison retains every point of the original relative conjugation family. -/
theorem boundedFlatPerfectBassTransitionHomotopy_apply (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space n) :
    Path.toContinuousMap ((boundedFlatPerfectBassTransitionHomotopy R).level n (r, x)) s =
      (BassInclusionTransitionTrack.conjugateComparison R).level n (r, (s, x)) := rfl

end Quillen.PerfectComplexes
