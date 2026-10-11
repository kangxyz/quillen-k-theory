/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSections
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionUnitNaturality

/-!
# The unchanged Laurent-unit action on actual supported sections

The original section-unit automorphism restricts through the fully faithful support inclusion.
Both its forward and inverse components remain the original section maps, and coefficient
naturality retains the whole specified open-pair square. Original evaluation therefore sees
the same geometric scalar action. This supplies the unit compatibility required by a supported
Bass seed; Waldhausen and seed constructions remain separate.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
variable {R S : CommRingCat.{u}} {U V : Scheme.{u}}

attribute [local irreducible] boundedFlatAffineOriginalEvaluation boundedFlatAffineEvaluationAt
  boundedFlatPerfectGlobalUnitIso

/-- Restrict the original global-unit automorphism to the actual supported section category. -/
def boundedFlatAffineSupportedSectionUnitIso (j : U ⟶ Spec R) [IsOpenImmersion j]
    (r : (Γ(Spec R, ⊤))ˣ) :
    𝟭 (BoundedFlatAffineSupportedSections j) ≅ 𝟭 (BoundedFlatAffineSupportedSections j) :=
  Quillen.FunctorIdentityAutomorphism.lift (boundedFlatAffineSectionSupported j).ι
    (boundedFlatAffineSectionUnitIso R r)

/-- Forgetting support retains the actual original forward scalar map. -/
theorem boundedFlatAffineSupportedSectionUnitIso_hom (j : U ⟶ Spec R) [IsOpenImmersion j]
    (r : (Γ(Spec R, ⊤))ˣ) (s : BoundedFlatAffineSupportedSections j) :
    ((boundedFlatAffineSupportedSectionUnitIso j r).hom.app s).hom =
      (boundedFlatAffineSectionUnitIso R r).hom.app s.obj :=
  Quillen.FunctorIdentityAutomorphism.map_lift_hom (boundedFlatAffineSectionSupported j).ι
    (boundedFlatAffineSectionUnitIso R r) s

/-- Forgetting support also retains the original inverse scalar map. -/
theorem boundedFlatAffineSupportedSectionUnitIso_inv (j : U ⟶ Spec R) [IsOpenImmersion j]
    (r : (Γ(Spec R, ⊤))ˣ) (s : BoundedFlatAffineSupportedSections j) :
    ((boundedFlatAffineSupportedSectionUnitIso j r).inv.app s).hom =
      (boundedFlatAffineSectionUnitIso R r).inv.app s.obj :=
  Quillen.FunctorIdentityAutomorphism.map_lift_inv (boundedFlatAffineSectionSupported j).ι
    (boundedFlatAffineSectionUnitIso R r) s

/-- The unchanged unit commutes strictly with the original supported coefficient restriction. -/
theorem boundedFlatAffineSupportedSectionUnitIso_coefficient_hom
    (j : U ⟶ Spec R) (j' : V ⟶ Spec S) [IsOpenImmersion j] [IsOpenImmersion j']
    (f : R ⟶ S) (l : V ⟶ U) (h : l ≫ j = j' ≫ Spec.map f)
    (r : (Γ(Spec R, ⊤))ˣ) :
    Functor.whiskerRight (boundedFlatAffineSupportedSectionUnitIso j r).hom
        (boundedFlatAffineSupportedSectionsMap j j' f l h) =
      Functor.whiskerLeft (boundedFlatAffineSupportedSectionsMap j j' f l h)
        (boundedFlatAffineSupportedSectionUnitIso j'
          (Units.map (Spec.map f).appTop.hom.toMonoidHom r)).hom := by
  apply NatTrans.ext
  funext s
  simp only [Functor.whiskerRight_app, Functor.whiskerLeft_app]
  apply ObjectProperty.hom_ext
  change (boundedFlatAffineSectionsMap f).map
    ((boundedFlatAffineSupportedSectionUnitIso j r).hom.app s).hom = _
  rw [boundedFlatAffineSupportedSectionUnitIso_hom, boundedFlatAffineSupportedSectionUnitIso_hom]
  exact NatTrans.congr_app (boundedFlatAffineSectionUnitIso_coefficient_hom f r) s.obj


end Quillen.PerfectComplexes
