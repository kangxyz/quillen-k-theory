/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionEquivalence
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalUnit
public import Quillen.CategoryTheory.Functor.IdentityAutomorphism

/-!
# Original global units on actual bounded-flat cocartesian sections

The proved fully faithful original evaluation lifts the original global-unit automorphism to a
natural automorphism of actual cocartesian sections. Both its forward and inverse actions evaluate
to the unchanged geometric scalar maps; no scalar or section replacement is chosen.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes

/-- The original geometric unit acts on the actual cocartesian section category. -/
def boundedFlatAffineSectionUnitIso (R : CommRingCat.{u}) (r : (Γ(Spec R, ⊤))ˣ) :
    𝟭 (BoundedFlatAffineSections R) ≅ 𝟭 (BoundedFlatAffineSections R) :=
  Quillen.FunctorIdentityAutomorphism.lift (boundedFlatAffineOriginalEvaluation R)
    (boundedFlatPerfectGlobalUnitIso (Spec R) r)

private theorem sectionUnitIso_eq (R : CommRingCat.{u}) (r : (Γ(Spec R, ⊤))ˣ) :
    boundedFlatAffineSectionUnitIso R r =
      Quillen.FunctorIdentityAutomorphism.lift (boundedFlatAffineOriginalEvaluation R)
        (boundedFlatPerfectGlobalUnitIso (Spec R) r) := rfl

/-- Original evaluation retains the actual geometric unit action on every section. -/
theorem boundedFlatAffineOriginalEvaluation_map_sectionUnitIso_hom (R : CommRingCat.{u})
    (r : (Γ(Spec R, ⊤))ˣ) (s : BoundedFlatAffineSections R) :
    (boundedFlatAffineOriginalEvaluation R).map
        ((boundedFlatAffineSectionUnitIso R r).hom.app s) =
      (boundedFlatPerfectGlobalUnitIso (Spec R) r).hom.app
        ((boundedFlatAffineOriginalEvaluation R).obj s) := by
  rw [sectionUnitIso_eq]
  exact Quillen.FunctorIdentityAutomorphism.map_lift_hom (boundedFlatAffineOriginalEvaluation R)
    (boundedFlatPerfectGlobalUnitIso (Spec R) r) s

/-- Original evaluation retains multiplication by the inverse original unit as well. -/
theorem boundedFlatAffineOriginalEvaluation_map_sectionUnitIso_inv (R : CommRingCat.{u})
    (r : (Γ(Spec R, ⊤))ˣ) (s : BoundedFlatAffineSections R) :
    (boundedFlatAffineOriginalEvaluation R).map
        ((boundedFlatAffineSectionUnitIso R r).inv.app s) =
      (boundedFlatPerfectGlobalUnitIso (Spec R) r).inv.app
        ((boundedFlatAffineOriginalEvaluation R).obj s) := by
  rw [sectionUnitIso_eq]
  exact Quillen.FunctorIdentityAutomorphism.map_lift_inv (boundedFlatAffineOriginalEvaluation R)
    (boundedFlatPerfectGlobalUnitIso (Spec R) r) s

end Quillen.PerfectComplexes
