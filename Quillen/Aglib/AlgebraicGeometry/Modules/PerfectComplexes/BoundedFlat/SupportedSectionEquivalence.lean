/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.SupportedSections
public import Quillen.Aglib.CategoryTheory.ObjectProperty.NestedEquivalence

/-!
# The genuine equivalence of original supported section evaluation

The existing original evaluation equivalence restricts to actual support and its nested target
is flattened by the proved categorical restriction equivalence. Its forward functor is literally
the existing supported evaluation, preserving original complexes and every chain map. No supported
model equivalence or negative localization is assumed.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
attribute [local irreducible] boundedFlatAffineOriginalEvaluation

/-- Original support is exactly the inverse-image predicate under the actual evaluation. -/
theorem boundedFlatAffineSupportedEvaluation_property :
    ((boundedFlatPerfectSupported j).inverseImage (boundedFlatPerfect (Spec R)).ι).inverseImage
        (boundedFlatAffineSectionEquivalence R).functor =
      boundedFlatAffineSectionSupported j := by
  funext s
  apply propext
  exact and_iff_right ((boundedFlatAffineOriginalEvaluation R).obj s).property

/-- Restrict the original equivalence and flatten the actual supported target, without replacement.
-/
def boundedFlatAffineSupportedSectionEquivalence :
    BoundedFlatAffineSupportedSections j ≌ (boundedFlatPerfectSupported j).FullSubcategory :=
  Quillen.ObjectProperty.evaluationRestrictionEquivalence
    (boundedFlatPerfect (Spec R)) (boundedFlatPerfectSupported j) (fun _ h ↦ h.1)
    (boundedFlatAffineSectionEquivalence R) (boundedFlatAffineSectionSupported j)
    (boundedFlatAffineSupportedEvaluation_property j)

/-- The forward equivalence is literally the original supported evaluation on objects and maps. -/
theorem boundedFlatAffineSupportedSectionEquivalence_functor :
    (boundedFlatAffineSupportedSectionEquivalence j).functor =
      boundedFlatAffineSupportedEvaluation j :=
  Quillen.ObjectProperty.evaluationRestrictionEquivalence_functor
    (boundedFlatPerfect (Spec R)) (boundedFlatPerfectSupported j) (fun _ h ↦ h.1)
    (boundedFlatAffineSectionEquivalence R) (boundedFlatAffineSectionSupported j)
    (boundedFlatAffineSupportedEvaluation_property j) _

instance boundedFlatAffineSupportedEvaluation_isEquivalence :
    (boundedFlatAffineSupportedEvaluation j).IsEquivalence := by
  rw [← boundedFlatAffineSupportedSectionEquivalence_functor]
  infer_instance

/-- The original counit supplies every original supported complex under the same evaluation. -/
def boundedFlatAffineSupportedEvaluationCounit
    (K : (boundedFlatPerfectSupported j).FullSubcategory) :
    (boundedFlatAffineSupportedEvaluation j).obj
      ((boundedFlatAffineSupportedSectionEquivalence j).inverse.obj K) ≅ K :=
  (boundedFlatAffineSupportedSectionEquivalence j).counitIso.app K

end Quillen.PerfectComplexes
