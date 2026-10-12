/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionForgetExact
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.OpenSupport

/-!
# Original supported section evaluation into relative acyclics

The original supported evaluation is followed by the proved geometric support-to-acyclic
functor. Its forward and inverse are genuinely exact, and the original section zero maps to
the inherited fine geometric zero. This retains the literal support inclusion for subsequent
null-track comparison without identifying independently chosen supported geometric zeros.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
open Waldhausen Waldhausen.Fibration
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
attribute [local irreducible] boundedFlatAffineOriginalEvaluation
  boundedFlatAffineSupportedSectionEquivalence boundedFlatAffineSupportedEvaluation

/-- Original supported evaluation followed by the actual support-to-acyclic conversion. -/
def boundedFlatAffineSupportedSectionAcyclicEvaluation :
    BoundedFlatAffineSupportedSections j ⥤ AcyclicCategory (boundedFlatPerfectOpenNested j) :=
  boundedFlatAffineSupportedEvaluation j ⋙ boundedFlatPerfectSupportedToAcyclic j

/-- The same actual supported functor is exact for the inherited fine classes. -/
theorem boundedFlatAffineSupportedSectionAcyclicEvaluation_exact :
    IsExact (boundedFlatAffineSupportedSectionWaldhausen j).cof
      (boundedFlatAffineSupportedSectionWaldhausen j).weq
      (acyclicStructure (boundedFlatPerfectOpenNested j)).cof
      (acyclicStructure (boundedFlatPerfectOpenNested j)).weq
      (boundedFlatAffineSupportedSectionAcyclicEvaluation j) :=
  (boundedFlatAffineSupportedEvaluation_exact j).comp
    (boundedFlatPerfectSupportedToAcyclic_exact j)

/-- Forgetting actual acyclicity retains the original support inclusion/evaluation composite. -/
theorem boundedFlatAffineSupportedSectionAcyclicEvaluation_inclusion :
    boundedFlatAffineSupportedSectionAcyclicEvaluation j ⋙
        acyclicInclusion (boundedFlatPerfectOpenNested j) =
      (boundedFlatAffineSectionSupported j).ι ⋙ boundedFlatAffineOriginalEvaluation R := by
  rw [boundedFlatAffineSupportedSectionAcyclicEvaluation, Functor.assoc,
    boundedFlatPerfectSupportedToAcyclic_comp_inclusion,
    boundedFlatAffineSupportedEvaluation_forget_to_boundedFlat]

/-- The genuine categorical equivalence keeps this exact original composite as forward functor. -/
def boundedFlatAffineSupportedSectionAcyclicEquivalence :
    BoundedFlatAffineSupportedSections j ≌ AcyclicCategory (boundedFlatPerfectOpenNested j) :=
  ((boundedFlatAffineSupportedSectionEquivalence j).trans
    (boundedFlatPerfectAcyclicSupportedEquivalence j).symm).changeFunctor
      (eqToIso (congrArg (fun F => F ⋙ boundedFlatPerfectSupportedToAcyclic j)
        (boundedFlatAffineSupportedSectionEquivalence_functor j)))

/-- Its original inverse retains the proved two fine exact inverses. -/
theorem boundedFlatAffineSupportedSectionAcyclicEquivalence_inverse_exact :
    IsExact (acyclicStructure (boundedFlatPerfectOpenNested j)).cof
      (acyclicStructure (boundedFlatPerfectOpenNested j)).weq
      (boundedFlatAffineSupportedSectionWaldhausen j).cof
      (boundedFlatAffineSupportedSectionWaldhausen j).weq
      (boundedFlatAffineSupportedSectionAcyclicEquivalence j).inverse :=
  (boundedFlatPerfectAcyclicToSupported_exact j).comp
    (boundedFlatAffineSupportedSectionEquivalence_inverse_exact j)

/-- The inherited acyclic zero is the actual image of the original supported section zero. -/
theorem boundedFlatAffineSupportedSectionAcyclicEvaluation_zero :
    (boundedFlatAffineSupportedSectionAcyclicEvaluation j).obj
        (boundedFlatAffineSupportedSectionWaldhausen j).zero =
      (acyclicStructure (boundedFlatPerfectOpenNested j)).zero := by
  apply ObjectProperty.FullSubcategory.ext
  have h := congrArg (fun F => F.obj (boundedFlatAffineSupportedSectionWaldhausen j).zero)
    (boundedFlatAffineSupportedSectionAcyclicEvaluation_inclusion j)
  refine h.trans ?_
  change (boundedFlatAffineOriginalEvaluation R).obj
      ((boundedFlatAffineSectionSupported j).ι.obj
        (boundedFlatAffineSupportedSectionWaldhausen j).zero) =
    (boundedFlatPerfectWaldhausen (Spec R)).zero
  rw [boundedFlatAffineSupportedSectionForget_zero, boundedFlatAffineSectionWaldhausen_zero,
    boundedFlatAffineOriginalEvaluation_sectionZero]

end Quillen.PerfectComplexes
