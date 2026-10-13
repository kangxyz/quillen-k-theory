/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionWaldhausen
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionWaldhausen
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionForgetEvaluation

/-!
# Exactness of original supported section inclusion

The original full-subcategory inclusion forgets only the actual support property. Its
commuting evaluation square and the geometric supported inclusion prove preservation of
zero objects, cofibrations, weak maps and pushouts. The chosen section zero is unchanged.
This supplies the original map toward localization, without a localization conclusion.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
attribute [local irreducible] boundedFlatAffineOriginalEvaluation
  boundedFlatAffineSupportedSectionEquivalence

/-- Original supported inclusion is exact after the unchanged original evaluation. -/
theorem boundedFlatAffineSupportedSectionForget_evaluation_exact :
    Waldhausen.IsExact (boundedFlatAffineSupportedSectionWaldhausen j).cof
      (boundedFlatAffineSupportedSectionWaldhausen j).weq
      (boundedFlatPerfectWaldhausen (Spec R)).cof (boundedFlatPerfectWaldhausen (Spec R)).weq
      ((boundedFlatAffineSectionSupported j).ι ⋙ boundedFlatAffineOriginalEvaluation R) := by
  rw [← boundedFlatAffineSupportedEvaluation_forget_to_boundedFlat]
  exact (boundedFlatAffineSupportedEvaluation_exact j).comp
    (Waldhausen.subcategoryInclusion_exact _ _ (fun _ h ↦ h.1))

/-- Forgetting actual section support preserves the original Waldhausen data. -/
theorem boundedFlatAffineSupportedSectionForget_exact :
    Waldhausen.IsExact (boundedFlatAffineSupportedSectionWaldhausen j).cof
      (boundedFlatAffineSupportedSectionWaldhausen j).weq
      (boundedFlatAffineSectionWaldhausen R).cof (boundedFlatAffineSectionWaldhausen R).weq
      (boundedFlatAffineSectionSupported j).ι where
  zero hx := IsZero.of_full_of_faithful_of_isZero (boundedFlatAffineOriginalEvaluation R) _
    ((boundedFlatAffineSupportedSectionForget_evaluation_exact j).zero hx)
  cofibration a ha := by
    change (boundedFlatPerfectWaldhausen (Spec R)).cof
      ((boundedFlatAffineOriginalEvaluation R).map _)
    exact (boundedFlatAffineSupportedSectionForget_evaluation_exact j).cofibration a ha
  weak a ha := by
    change (boundedFlatPerfectWaldhausen (Spec R)).weq
      ((boundedFlatAffineOriginalEvaluation R).map _)
    exact (boundedFlatAffineSupportedSectionForget_evaluation_exact j).weak a ha
  pushout hi hp := by
    apply IsPushout.of_map_of_faithful (boundedFlatAffineOriginalEvaluation R)
    exact (boundedFlatAffineSupportedSectionForget_evaluation_exact j).pushout hi hp

/-- The literal chosen section zero survives the original inclusion. -/
theorem boundedFlatAffineSupportedSectionForget_zero :
    (boundedFlatAffineSectionSupported j).ι.obj
        (boundedFlatAffineSupportedSectionWaldhausen j).zero =
      (boundedFlatAffineSectionWaldhausen R).zero := rfl

end Quillen.PerfectComplexes
