/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionOpenKComparison

/-! The actual relative-open comparison lifts original classes before full-open restriction. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.PerfectComplexes
universe u
namespace Quillen.Tests.SectionOpenKComparison
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The inverse returns the same relative-open section object class, including its original zero. -/
theorem original_relative_object_class_inverse (S : BoundedFlatAffineSections R) :
    (boundedFlatAffineSectionOpenPerfectKEquiv j 0).symm
        ((perfectOpenWeakWaldhausen j).kZeroObjectClass
          ((boundedFlatPerfectInclusion (Spec R)).obj
            ((boundedFlatAffineOriginalEvaluation R).obj S))) =
      (boundedFlatAffineSectionOpenWaldhausen j).kZeroObjectClass S := by
  rw [← boundedFlatAffineSectionOpenPerfectKEquiv_objectClass j S,
    MulEquiv.symm_apply_apply]

/-- The original relative-perfect class has a preimage before applying any full-open restriction. -/
theorem original_relative_class_preimage (n : ℕ)
    (x : (perfectOpenWeakWaldhausen j).K n) :
    ∃ y : (boundedFlatAffineSectionOpenWaldhausen j).K n,
      boundedFlatAffineSectionOpenPerfectKEquiv j n y = x :=
  (boundedFlatAffineSectionOpenPerfectKEquiv j n).surjective x

end Quillen.Tests.SectionOpenKComparison
