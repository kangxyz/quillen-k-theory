/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionRestriction
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionWaldhausen
public import Quillen.CategoryTheory.FiberedCategory.GrothendieckUnderRestrictionEvaluation

/-!
# Evaluation of the actual full-open section restriction

The original section restriction evaluates to the unchanged affine evaluation followed by
its specified open pullback. The generic equality retains the actual vertical inclusion,
rebracketing and strong-transformation unit comparison. It chooses no inverse evaluation.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Scheme.AffineOpenPair
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The original section comparison has exactly the original evaluation composite. -/
theorem boundedFlatAffineFullOpenSectionRestriction_comp_evaluation (a : Under R) :
    boundedFlatAffineFullOpenSectionRestriction j a ⋙
        boundedFlatAffineFullOpenOriginalEvaluation j a =
      boundedFlatAffineSectionFullOpenRestriction j a := by
  have h := Quillen.CategoryTheory.GrothendieckUnderRestriction.sectionFunctor_comp_evaluation
    Scheme.Spec.rightOp boundedFlatPerfectPseudofunctor R
    (boundedFlatAffineFullOpenPseudofunctor j)
    (boundedFlatAffineFullOpenRestrictionStrongTrans j) a
  change boundedFlatAffineFullOpenSectionRestriction j a ⋙
      boundedFlatAffineFullOpenOriginalEvaluation j a =
    boundedFlatAffineOriginalEvaluation a.right ⋙
      ((boundedFlatAffineFullOpenRestrictionStrongTrans j).app ⟨a⟩).toFunctor at h
  rw [boundedFlatAffineFullOpenRestrictionStrongTrans_app] at h
  exact h

end Quillen.PerfectComplexes
