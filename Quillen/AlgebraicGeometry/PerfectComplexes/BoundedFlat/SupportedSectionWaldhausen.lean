/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionEquivalence
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionZero
public import Quillen.Waldhausen.EquivalenceStructure

/-!
# Genuine Waldhausen structure on original supported affine sections

The proved original supported evaluation equivalence transports the original geometric
cofibrations, weak equivalences and pushouts. The chosen zero is the same source-independent
supported section proved earlier. Both directions of that actual equivalence are exact.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
attribute [local irreducible] boundedFlatAffineOriginalEvaluation
  boundedFlatAffineSupportedSectionEquivalence boundedFlatAffineSupportedEvaluation

private theorem equivalence_obj_isZero {C D : Type*} [Category* C] [Category* D]
    (e : C ≌ D) {X : C} (hX : IsZero X) : IsZero (e.functor.obj X) :=
  IsZero.of_full_of_faithful_of_isZero e.inverse _ (hX.of_iso (e.unitIso.app X).symm)

/-- Actual supported evaluation carries the original chosen section to a genuine zero object. -/
theorem boundedFlatAffineSupportedEvaluation_sectionZero_isZero :
    IsZero ((boundedFlatAffineSupportedEvaluation j).obj
      (boundedFlatAffineSupportedSectionZero j)) := by
  rw [← boundedFlatAffineSupportedSectionEquivalence_functor]
  exact equivalence_obj_isZero (boundedFlatAffineSupportedSectionEquivalence j)
    (isZero_boundedFlatAffineSupportedSectionZero j)

/-- Original supported morphism classes and pushouts, with the unchanged chosen zero section. -/
def boundedFlatAffineSupportedSectionWaldhausen :
    Waldhausen.Structure (BoundedFlatAffineSupportedSections j) :=
  (boundedFlatPerfectSupportedWaldhausen j).ofEquivalence
    (boundedFlatAffineSupportedSectionEquivalence j) (boundedFlatAffineSupportedSectionZero j)
    (by rw [boundedFlatAffineSupportedSectionEquivalence_functor]
        exact boundedFlatAffineSupportedEvaluation_sectionZero_isZero j)

/-- The chosen zero retains the exact original supported section. -/
theorem boundedFlatAffineSupportedSectionWaldhausen_zero :
    (boundedFlatAffineSupportedSectionWaldhausen j).zero =
      boundedFlatAffineSupportedSectionZero j := rfl

/-- Cofibrations are precisely the original geometric supported cofibrations under evaluation. -/
theorem boundedFlatAffineSupportedSectionWaldhausen_cof_iff
    {X Y : BoundedFlatAffineSupportedSections j} (f : X ⟶ Y) :
    (boundedFlatAffineSupportedSectionWaldhausen j).cof f ↔
      (boundedFlatPerfectSupportedWaldhausen j).cof
        ((boundedFlatAffineSupportedEvaluation j).map f) := by
  change (boundedFlatPerfectSupportedWaldhausen j).cof
    ((boundedFlatAffineSupportedSectionEquivalence j).functor.map f) ↔ _
  rw [boundedFlatAffineSupportedSectionEquivalence_functor]

/-- Weak equivalences are the original geometric supported weak maps under evaluation. -/
theorem boundedFlatAffineSupportedSectionWaldhausen_weq_iff
    {X Y : BoundedFlatAffineSupportedSections j} (f : X ⟶ Y) :
    (boundedFlatAffineSupportedSectionWaldhausen j).weq f ↔
      (boundedFlatPerfectSupportedWaldhausen j).weq
        ((boundedFlatAffineSupportedEvaluation j).map f) := by
  change (boundedFlatPerfectSupportedWaldhausen j).weq
    ((boundedFlatAffineSupportedSectionEquivalence j).functor.map f) ↔ _
  rw [boundedFlatAffineSupportedSectionEquivalence_functor]

/-- The original supported evaluation is exact for these genuinely constructed structures. -/
theorem boundedFlatAffineSupportedEvaluation_exact :
    Waldhausen.IsExact (boundedFlatAffineSupportedSectionWaldhausen j).cof
      (boundedFlatAffineSupportedSectionWaldhausen j).weq
      (boundedFlatPerfectSupportedWaldhausen j).cof (boundedFlatPerfectSupportedWaldhausen j).weq
      (boundedFlatAffineSupportedEvaluation j) := by
  rw [← boundedFlatAffineSupportedSectionEquivalence_functor]
  exact Waldhausen.Structure.ofEquivalence_exact _ _ _ _

/-- The same actual supported inverse equivalence is also Waldhausen-exact. -/
theorem boundedFlatAffineSupportedSectionEquivalence_inverse_exact :
    Waldhausen.IsExact (boundedFlatPerfectSupportedWaldhausen j).cof
      (boundedFlatPerfectSupportedWaldhausen j).weq
      (boundedFlatAffineSupportedSectionWaldhausen j).cof
      (boundedFlatAffineSupportedSectionWaldhausen j).weq
      (boundedFlatAffineSupportedSectionEquivalence j).inverse :=
  Waldhausen.Structure.ofEquivalence_inverse_exact _ _ _ _

end Quillen.PerfectComplexes
