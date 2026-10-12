/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenGradedSectionStable

/-! An independent client uses concentration on both sides of an original graded Model map. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.PerfectComplexes Quillen.Waldhausen.IteratedS
universe u
namespace Consumer.FullOpenGradedSectionStable
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The unchanged map of actual graded section Models is invertible in each nonzero degree. -/
theorem original_model_map_isIso_of_ne_zero {a b : Under R}
    (F : boundedFlatAffineFullOpenGradedSectionModel j a ⟶
      boundedFlatAffineFullOpenGradedSectionModel j b) (d : ℤ) (hd : d ≠ 0) :
    IsIso ((stableHomotopyFunctor d).map (prespectrumMap F)) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  have hA := boundedFlatAffineFullOpenGradedSection_stable_subsingleton j a d hd
  have hB := boundedFlatAffineFullOpenGradedSection_stable_subsingleton j b d hd
  exact ⟨fun _ _ _ ↦ hA.elim _ _, fun _ ↦ ⟨0, hB.elim _ _⟩⟩

end Consumer.FullOpenGradedSectionStable
