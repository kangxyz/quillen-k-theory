/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionReindex
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalUnitPullback
public import Quillen.CategoryTheory.Functor.IdentityAutomorphismNaturality

/-!
# Original global units on actual full-open sections

The fully faithful original evaluation lifts the unchanged geometric global-unit automorphism
onto the actual full-open section category. Original coefficient reindexing commutes with this
action: the proof retains its genuine evaluation comparison and the actual geometric pullback.
For a unit on the original affine ambient scheme, restriction and coefficient pullback give the
same target unit by the original open-pair square. No flatness of a coefficient arrow is required.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Scheme.AffineOpenPair
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
attribute [local irreducible] boundedFlatAffineFullOpenOriginalEvaluation
  boundedFlatPerfectGlobalUnitIso

/-- The original geometric unit acts on the actual full-open section category. -/
def boundedFlatAffineFullOpenSectionUnitIso (a : Under R)
    (r : (Γ(openSpace j a, ⊤))ˣ) :
    𝟭 (BoundedFlatAffineFullOpenSections j a) ≅ 𝟭 (BoundedFlatAffineFullOpenSections j a) :=
  Quillen.FunctorIdentityAutomorphism.lift (boundedFlatAffineFullOpenOriginalEvaluation j a)
    (boundedFlatPerfectGlobalUnitIso (openSpace j a) r)

private theorem fullOpenSectionUnitIso_eq (a : Under R)
    (r : (Γ(openSpace j a, ⊤))ˣ) :
    boundedFlatAffineFullOpenSectionUnitIso j a r =
      Quillen.FunctorIdentityAutomorphism.lift (boundedFlatAffineFullOpenOriginalEvaluation j a)
        (boundedFlatPerfectGlobalUnitIso (openSpace j a) r) := rfl

/-- Original evaluation retains the unchanged forward unit on every actual section. -/
theorem boundedFlatAffineFullOpenOriginalEvaluation_map_sectionUnitIso_hom (a : Under R)
    (r : (Γ(openSpace j a, ⊤))ˣ) (s : BoundedFlatAffineFullOpenSections j a) :
    (boundedFlatAffineFullOpenOriginalEvaluation j a).map
        ((boundedFlatAffineFullOpenSectionUnitIso j a r).hom.app s) =
      (boundedFlatPerfectGlobalUnitIso (openSpace j a) r).hom.app
        ((boundedFlatAffineFullOpenOriginalEvaluation j a).obj s) := by
  rw [fullOpenSectionUnitIso_eq]
  exact Quillen.FunctorIdentityAutomorphism.map_lift_hom
    (boundedFlatAffineFullOpenOriginalEvaluation j a)
    (boundedFlatPerfectGlobalUnitIso (openSpace j a) r) s

/-- Original evaluation retains the inverse component of the same original automorphism. -/
theorem boundedFlatAffineFullOpenOriginalEvaluation_map_sectionUnitIso_inv (a : Under R)
    (r : (Γ(openSpace j a, ⊤))ˣ) (s : BoundedFlatAffineFullOpenSections j a) :
    (boundedFlatAffineFullOpenOriginalEvaluation j a).map
        ((boundedFlatAffineFullOpenSectionUnitIso j a r).inv.app s) =
      (boundedFlatPerfectGlobalUnitIso (openSpace j a) r).inv.app
        ((boundedFlatAffineFullOpenOriginalEvaluation j a).obj s) := by
  rw [fullOpenSectionUnitIso_eq]
  exact Quillen.FunctorIdentityAutomorphism.map_lift_inv
    (boundedFlatAffineFullOpenOriginalEvaluation j a)
    (boundedFlatPerfectGlobalUnitIso (openSpace j a) r) s

/-- The entire evaluated component is the specified original geometric unit automorphism. -/
theorem boundedFlatAffineFullOpenOriginalEvaluation_mapIso_sectionUnitIso (a : Under R)
    (r : (Γ(openSpace j a, ⊤))ˣ) (s : BoundedFlatAffineFullOpenSections j a) :
    (boundedFlatAffineFullOpenOriginalEvaluation j a).mapIso
        ((boundedFlatAffineFullOpenSectionUnitIso j a r).app s) =
      (boundedFlatPerfectGlobalUnitIso (openSpace j a) r).app
        ((boundedFlatAffineFullOpenOriginalEvaluation j a).obj s) :=
  Quillen.FunctorIdentityAutomorphism.mapIso_app_eq
    (boundedFlatAffineFullOpenOriginalEvaluation j a)
    (boundedFlatAffineFullOpenSectionUnitIso j a r)
    (boundedFlatPerfectGlobalUnitIso (openSpace j a) r) s
    (boundedFlatAffineFullOpenOriginalEvaluation_map_sectionUnitIso_hom j a r s)

/-- The genuine coefficient comparison retains the actual pulled-back forward unit. -/
theorem boundedFlatAffineFullOpenSectionsMap_evaluation_map_sectionUnitIso_hom
    {a b : Under R} (f : a ⟶ b) (r : (Γ(openSpace j a, ⊤))ˣ)
    (s : BoundedFlatAffineFullOpenSections j a) :
    (boundedFlatAffineFullOpenOriginalEvaluation j b).map
        ((boundedFlatAffineFullOpenSectionsMap j f).map
          ((boundedFlatAffineFullOpenSectionUnitIso j a r).hom.app s)) =
      (boundedFlatPerfectGlobalUnitIso (openSpace j b)
        (Units.map (openMap j f).appTop.hom.toMonoidHom r)).hom.app
          ((boundedFlatAffineFullOpenOriginalEvaluation j b).obj
            ((boundedFlatAffineFullOpenSectionsMap j f).obj s)) := by
  exact Quillen.FunctorIdentityAutomorphism.map_hom_eq_of_iso
    (boundedFlatAffineFullOpenSectionsMap j f ⋙
      boundedFlatAffineFullOpenOriginalEvaluation j b)
    (boundedFlatAffineFullOpenOriginalEvaluation j a ⋙
      boundedFlatPerfectPullback (openMap j f))
    (boundedFlatAffineFullOpenSectionCoefficientIso j f)
    (boundedFlatAffineFullOpenSectionUnitIso j a r)
    (boundedFlatPerfectGlobalUnitIso (openSpace j b)
      (Units.map (openMap j f).appTop.hom.toMonoidHom r))
    (fun t => by
      change (boundedFlatPerfectPullback (openMap j f)).map
        ((boundedFlatAffineFullOpenOriginalEvaluation j a).map
          ((boundedFlatAffineFullOpenSectionUnitIso j a r).hom.app t)) = _
      rw [boundedFlatAffineFullOpenOriginalEvaluation_map_sectionUnitIso_hom,
        boundedFlatPerfectPullback_map_globalUnit]
      simp only [Functor.comp_obj]) s

/-- The original section automorphism commutes strictly with every coefficient reindexing. -/
theorem boundedFlatAffineFullOpenSectionUnitIso_coefficient_hom {a b : Under R}
    (f : a ⟶ b) (r : (Γ(openSpace j a, ⊤))ˣ) :
    Functor.whiskerRight (boundedFlatAffineFullOpenSectionUnitIso j a r).hom
        (boundedFlatAffineFullOpenSectionsMap j f) =
      Functor.whiskerLeft (boundedFlatAffineFullOpenSectionsMap j f)
        (boundedFlatAffineFullOpenSectionUnitIso j b
          (Units.map (openMap j f).appTop.hom.toMonoidHom r)).hom := by
  exact Quillen.FunctorIdentityAutomorphism.whisker_hom_eq_of_evaluation
    (boundedFlatAffineFullOpenSectionsMap j f)
    (boundedFlatAffineFullOpenOriginalEvaluation j b)
    (boundedFlatAffineFullOpenSectionsMap j f ⋙
      boundedFlatAffineFullOpenOriginalEvaluation j b) rfl
    (boundedFlatAffineFullOpenSectionUnitIso j a r)
    (boundedFlatAffineFullOpenSectionUnitIso j b
      (Units.map (openMap j f).appTop.hom.toMonoidHom r))
    (boundedFlatPerfectGlobalUnitIso (openSpace j b)
      (Units.map (openMap j f).appTop.hom.toMonoidHom r))
    (boundedFlatAffineFullOpenSectionsMap_evaluation_map_sectionUnitIso_hom j f r)
    (boundedFlatAffineFullOpenOriginalEvaluation_map_sectionUnitIso_hom j b
      (Units.map (openMap j f).appTop.hom.toMonoidHom r))

omit [IsOpenImmersion j] in
/-- Original ambient restriction and original coefficient pullback give the identical unit. -/
theorem boundedFlatAffineFullOpenUnit_coefficient {a b : Under R}
    (f : a ⟶ b) (r : (Γ(Spec a.right, ⊤))ˣ) :
    Units.map (openMap j f).appTop.hom.toMonoidHom
        (boundedFlatAffineFullOpenUnit j a r) =
      boundedFlatAffineFullOpenUnit j b
        (Units.map (Spec.map f.right).appTop.hom.toMonoidHom r) := by
  apply Units.ext
  have h := congrArg (fun g => g.appTop) (openMap_inclusion j f)
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h
  exact ConcreteCategory.congr_hom h (↑r)

/-- The categorical coefficient square retains the original ambient unit and its orientation. -/
theorem boundedFlatAffineFullOpenSectionUnitIso_original_coefficient_hom {a b : Under R}
    (f : a ⟶ b) (r : (Γ(Spec a.right, ⊤))ˣ) :
    Functor.whiskerRight
        (boundedFlatAffineFullOpenSectionUnitIso j a (boundedFlatAffineFullOpenUnit j a r)).hom
        (boundedFlatAffineFullOpenSectionsMap j f) =
      Functor.whiskerLeft (boundedFlatAffineFullOpenSectionsMap j f)
        (boundedFlatAffineFullOpenSectionUnitIso j b (boundedFlatAffineFullOpenUnit j b
          (Units.map (Spec.map f.right).appTop.hom.toMonoidHom r))).hom := by
  rw [← boundedFlatAffineFullOpenUnit_coefficient j f r]
  exact boundedFlatAffineFullOpenSectionUnitIso_coefficient_hom j f
    (boundedFlatAffineFullOpenUnit j a r)

end Quillen.PerfectComplexes
