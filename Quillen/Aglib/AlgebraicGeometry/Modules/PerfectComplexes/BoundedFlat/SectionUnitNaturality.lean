/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.SectionUnitAction
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.SectionEvaluation
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.GlobalUnitPullback

/-!
# Pointwise original unit action and strict coefficient naturality

Evaluation at every original coefficient arrow carries the section automorphism to multiplication
by the pulled-back original global unit. The actual evaluation transition proves this formula.
It implies strict naturality under literal coefficient reindexing, without a replacement action.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes

attribute [local irreducible] boundedFlatAffineOriginalEvaluation boundedFlatAffineEvaluationAt
  boundedFlatPerfectGlobalUnitIso

/-- Every original arrow evaluation sees the original pulled-back global-unit scalar. -/
theorem boundedFlatAffineEvaluationAt_map_sectionUnitIso_hom (R : CommRingCat.{u})
    (r : (Γ(Spec R, ⊤))ˣ) (s : BoundedFlatAffineSections R) (j : Under R) :
    (boundedFlatAffineEvaluationAt R j).map ((boundedFlatAffineSectionUnitIso R r).hom.app s) =
      (boundedFlatPerfectGlobalUnitIso (Spec j.right)
        (Units.map (Spec.map j.hom).appTop.hom.toMonoidHom r)).hom.app
          ((boundedFlatAffineEvaluationAt R j).obj s) := by
  have h₁ := boundedFlatAffineEvaluationPullbackIso_naturality R
    ((boundedFlatAffineSectionUnitIso R r).hom.app s) j
  rw [boundedFlatAffineOriginalEvaluation_map_sectionUnitIso_hom,
    boundedFlatPerfectPullback_map_globalUnit] at h₁
  have h₂ := (boundedFlatPerfectGlobalUnitIso (Spec j.right)
    (Units.map (Spec.map j.hom).appTop.hom.toMonoidHom r)).hom.naturality
      ((boundedFlatAffineEvaluationPullbackIso R j).hom.app s)
  simp only [Functor.id_map] at h₂
  exact (cancel_epi ((boundedFlatAffineEvaluationPullbackIso R j).hom.app s)).mp
    (h₁.symm.trans h₂.symm)

/-- The entire evaluated automorphism is the original geometric pulled-back unit automorphism. -/
theorem boundedFlatAffineEvaluationAt_mapIso_sectionUnitIso (R : CommRingCat.{u})
    (r : (Γ(Spec R, ⊤))ˣ) (s : BoundedFlatAffineSections R) (j : Under R) :
    (boundedFlatAffineEvaluationAt R j).mapIso ((boundedFlatAffineSectionUnitIso R r).app s) =
      (boundedFlatPerfectGlobalUnitIso (Spec j.right)
        (Units.map (Spec.map j.hom).appTop.hom.toMonoidHom r)).app
          ((boundedFlatAffineEvaluationAt R j).obj s) := by
  exact Quillen.FunctorIdentityAutomorphism.mapIso_app_eq
    (boundedFlatAffineEvaluationAt R j) (boundedFlatAffineSectionUnitIso R r)
    (boundedFlatPerfectGlobalUnitIso (Spec j.right)
      (Units.map (Spec.map j.hom).appTop.hom.toMonoidHom r)) s
    (boundedFlatAffineEvaluationAt_map_sectionUnitIso_hom R r s j)

/-- The inverse section action retains the inverse original scalar at every coefficient arrow. -/
theorem boundedFlatAffineEvaluationAt_map_sectionUnitIso_inv (R : CommRingCat.{u})
    (r : (Γ(Spec R, ⊤))ˣ) (s : BoundedFlatAffineSections R) (j : Under R) :
    (boundedFlatAffineEvaluationAt R j).map ((boundedFlatAffineSectionUnitIso R r).inv.app s) =
      (boundedFlatPerfectGlobalUnitIso (Spec j.right)
        (Units.map (Spec.map j.hom).appTop.hom.toMonoidHom r)).inv.app
          ((boundedFlatAffineEvaluationAt R j).obj s) := by
  exact Quillen.FunctorIdentityAutomorphism.map_inv_app_eq
    (boundedFlatAffineEvaluationAt R j) (boundedFlatAffineSectionUnitIso R r)
    (boundedFlatPerfectGlobalUnitIso (Spec j.right)
      (Units.map (Spec.map j.hom).appTop.hom.toMonoidHom r)) s
    (boundedFlatAffineEvaluationAt_map_sectionUnitIso_hom R r s j)

/-- The actual section automorphism commutes with every original transition of its section. -/
theorem boundedFlatAffineSectionUnitIso_section_naturality (R : CommRingCat.{u})
    (r : (Γ(Spec R, ⊤))ˣ) (s : BoundedFlatAffineSections R) {i j : Under R} (a : i ⟶ j) :
    let φ : s ⟶ s := (boundedFlatAffineSectionUnitIso R r).hom.app s
    s.obj.val.map a ≫ φ.hom.val.app j = φ.hom.val.app i ≫ s.obj.val.map a := by
  exact (fun φ : s ⟶ s ↦ φ.hom.val.naturality a)
    ((boundedFlatAffineSectionUnitIso R r).hom.app s)

/-- Original units commute strictly with literal coefficient restriction of sections. -/
theorem boundedFlatAffineSectionUnitIso_coefficient_hom {R S : CommRingCat.{u}}
    (f : R ⟶ S) (r : (Γ(Spec R, ⊤))ˣ) :
    Functor.whiskerRight (boundedFlatAffineSectionUnitIso R r).hom
        (boundedFlatAffineSectionsMap f) =
      Functor.whiskerLeft (boundedFlatAffineSectionsMap f)
        (boundedFlatAffineSectionUnitIso S
          (Units.map (Spec.map f).appTop.hom.toMonoidHom r)).hom := by
  exact Quillen.FunctorIdentityAutomorphism.whisker_hom_eq_of_evaluation
    (boundedFlatAffineSectionsMap f) (boundedFlatAffineOriginalEvaluation S)
    (boundedFlatAffineEvaluationAt R (Under.mk f))
    (boundedFlatAffineSectionsMap_comp_evaluation f)
    (boundedFlatAffineSectionUnitIso R r)
    (boundedFlatAffineSectionUnitIso S (Units.map (Spec.map f).appTop.hom.toMonoidHom r))
    (boundedFlatPerfectGlobalUnitIso (Spec S) (Units.map (Spec.map f).appTop.hom.toMonoidHom r))
    (fun s ↦ boundedFlatAffineEvaluationAt_map_sectionUnitIso_hom R r s (Under.mk f))
    (boundedFlatAffineOriginalEvaluation_map_sectionUnitIso_hom S
      (Units.map (Spec.map f).appTop.hom.toMonoidHom r))

end Quillen.PerfectComplexes
