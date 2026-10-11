/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSections
public import Quillen.CategoryTheory.ObjectProperty.LiftInclusion

/-!
# Original supported evaluation and forgetting support

Forgetting only geometric support after actual evaluation gives the unchanged ambient
section evaluation functor. A generic precomposed lift identity retains its literal maps
without reassociating the large geometric functors. Exactness is proved in the next owner.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
attribute [local irreducible] boundedFlatAffineOriginalEvaluation


/-- Forgetting geometric support after original evaluation retains the original section functor. -/
theorem boundedFlatAffineSupportedEvaluation_forget_to_boundedFlat :
    boundedFlatAffineSupportedEvaluation j ⋙ ObjectProperty.ιOfLE
        (show boundedFlatPerfectSupported j ≤ boundedFlatPerfect (Spec R) from fun _ h ↦ h.1) =
      (boundedFlatAffineSectionSupported j).ι ⋙ boundedFlatAffineOriginalEvaluation R :=
  Quillen.ObjectProperty.lift_comp_ιOfLE_comp
    (boundedFlatPerfectSupported j) (boundedFlatPerfect (Spec R)) (fun _ h ↦ h.1)
    (boundedFlatAffineSectionSupported j).ι (boundedFlatAffineOriginalEvaluation R)
    (fun s ↦ ⟨((boundedFlatAffineOriginalEvaluation R).obj s.obj).property, s.property⟩)


end Quillen.PerfectComplexes
