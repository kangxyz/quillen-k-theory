/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenGradedSectionBassTransitionNull

/-!
# Consumers of the original graded transition null

The initial iterate preserves the exact prescribed seed-null loop. Every finite original
transition vanishes also in negative signed degrees, and null and structure coordinates remain
independent at every stage. No localization-null or connectivity premise is introduced.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PolynomialBaseChange Quillen.LoopPrespectrum
open Quillen.KTheory.Bass Quillen.PerfectComplexes
universe u
namespace Quillen.Tests.FullOpenGradedSectionBassTransitionNull
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R)
  [IsOpenImmersion j] [CompactSpace U]

/-- The original joint seed-null family remains literal at stage zero and every loop coordinate. -/
theorem graded_transition_zero_original_loop (a : Under R) (n : ℕ) (r s : unitInterval)
    (x : ((boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j).obj a).space n) :
    Path.toContinuousMap
        ((boundedFlatAffineFullOpenGradedSectionBassTransitionNullHomotopy j 0 a).level n
          (r, x)) s =
      (boundedFlatAffineFullOpenGradedSectionBassSeedNullComparison j a).level n (r, (s, x)) :=
  boundedFlatAffineFullOpenGradedSectionBassSeedNullHomotopy_apply j a n r s x

/-- Negative signed degrees use the same actual outgoing transition map, with no degree cutoff. -/
theorem graded_transition_negative_stable_zero (k m : ℕ) (a : Under R) :
    (stableHomotopyFunctor (-(m : ℤ) - 1)).map
      ((strictDiagramTransition (laurentUnderSquareFunctor R)
        (boundedFlatAffineFullOpenGradedSectionBassSeed j) k).app a) = 0 :=
  boundedFlatAffineFullOpenGradedSectionBassTransition_stableMap_eq_zero j k a _

/-- The prescribed null and independent structure time commute at every original finite stage. -/
theorem graded_transition_independent_structure (k : ℕ) (a : Under R) (n : ℕ)
    (r t : unitInterval)
    (x : (((strictDiagramIterate (laurentUnderSquareFunctor R) k).obj
      (boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j)).obj a).space n) :
    (boundedFlatAffineFullOpenGradedSectionBassTransitionNullHomotopy j k a).level (n + 1)
        (r, (((strictDiagramIterate (laurentUnderSquareFunctor R) k).obj
          (boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j)).obj a).structureMap n x t) =
      (((strictDiagramIterate (laurentUnderSquareFunctor R) (k + 1)).obj
        (boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j)).obj a).structureMap n
          ((boundedFlatAffineFullOpenGradedSectionBassTransitionNullHomotopy j k a).level n
            (r, x)) t :=
  (boundedFlatAffineFullOpenGradedSectionBassTransitionNullHomotopy j k a).comm n r x t

end Quillen.Tests.FullOpenGradedSectionBassTransitionNull
