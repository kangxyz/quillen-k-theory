/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenGradedSectionStable

/-! Consumers keep both the actual section stable groups and the original graded K-groups. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.PerfectComplexes Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.Tests.FullOpenGradedSectionStable
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- A class in the unchanged stable group is zero in every nonzero signed degree. -/
theorem original_stable_class_eq_zero (a : Under R) (d : ℤ) (hd : d ≠ 0)
    (x : stableHomotopyGroup
      (prespectrum (boundedFlatAffineFullOpenGradedSectionModel j a)) d) : x = 0 := by
  let := boundedFlatAffineFullOpenGradedSection_stable_subsingleton j a d hd
  exact Subsingleton.elim _ _

/-- The direct level-one comparison recovers equality in the original multiplicative K-group. -/
theorem original_positive_K_class_eq_one (a : Under R) (n : ℕ)
    (x : (boundedFlatAffineFullOpenSectionGrading j a).coarseStructure.K (n + 1)) : x = 1 := by
  let := boundedFlatAffineFullOpenGradedSection_stable_succ_subsingleton j a n
  let e : Additive ((boundedFlatAffineFullOpenSectionGrading j a).coarseStructure.K (n + 1)) ≃+
      stableHomotopyGroup
        (prespectrum (boundedFlatAffineFullOpenGradedSectionModel j a)) ((n + 1 : ℕ) : ℤ) :=
    levelOneStableEquiv (prespectrum (boundedFlatAffineFullOpenGradedSectionModel j a))
      (prespectrum_isOmega (boundedFlatAffineFullOpenGradedSectionModel j a)) (n + 1)
  apply Additive.ofMul.injective
  apply e.injective
  exact Subsingleton.elim _ _

/-- Every actual incoming prespectrum map has zero value in a nonzero signed target degree. -/
theorem original_incoming_stable_map_eq_zero (a : Under R) {E : LoopPrespectrum.{u + 1}}
    (f : E ⟶ prespectrum (boundedFlatAffineFullOpenGradedSectionModel j a))
    (d : ℤ) (hd : d ≠ 0) (x : stableHomotopyGroup E d) :
    (stableHomotopyFunctor d).map f x = 0 := by
  let h : Subsingleton (stableHomotopyGroup
      (prespectrum (boundedFlatAffineFullOpenGradedSectionModel j a)) d) :=
    boundedFlatAffineFullOpenGradedSection_stable_subsingleton j a d hd
  exact h.elim _ _

end Quillen.Tests.FullOpenGradedSectionStable
