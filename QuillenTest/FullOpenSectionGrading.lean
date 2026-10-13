/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionGrading

/-! Consumers retain the original image quotient and the inherited section zero. -/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.PerfectComplexes Quillen.Scheme.AffineOpenPair
universe u
namespace QuillenTest.FullOpenSectionGrading

open Quillen
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The original evaluated object supplies its unchanged raw-perfect quotient grade. -/
theorem original_grade (a : Under R) (S : BoundedFlatAffineFullOpenSections j a) :
    (boundedFlatAffineFullOpenSectionGrading j a).value S =
      (perfectOpenDeficitGrading (inclusion j a)).value
        ((boundedFlatAffineFullOpenPerfectEvaluation j a).obj S) :=
  boundedFlatAffineFullOpenSectionGrading_value j a S

/-- The grading retains the single original inherited global zero section. -/
theorem original_zero (a : Under R) :
    (boundedFlatAffineFullOpenGradedSectionModel j a).waldhausen.zero =
      boundedFlatAffineFullOpenSectionZero j a := rfl

/-- Every actual endomorphism is weak by equality of its original endpoint grade. -/
theorem original_endomorphism_weak (a : Under R)
    (S : BoundedFlatAffineFullOpenSections j a) (f : S ⟶ S) :
    (boundedFlatAffineFullOpenSectionGrading j a).coarseStructure.weq f := rfl

/-- Exactness proves the genuine image object is zero without replacing it by a chosen object. -/
theorem original_zero_image_isZero (a : Under R) :
    IsZero ((boundedFlatAffineFullOpenPerfectEvaluation j a).obj
      (boundedFlatAffineFullOpenSectionWaldhausen j a).zero) :=
  (boundedFlatAffineFullOpenPerfectEvaluation_exact j a).zero
    (boundedFlatAffineFullOpenSectionWaldhausen j a).isZero

end QuillenTest.FullOpenSectionGrading
