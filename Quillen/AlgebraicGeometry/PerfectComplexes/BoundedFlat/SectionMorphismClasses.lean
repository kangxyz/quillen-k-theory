/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.SectionEvaluation

/-!
# Actual pointwise morphism classes on bounded-flat sections

Cofibrations and weak equivalences are required at every original fiber. The original geometric
pullback comparison proves that these are exactly the classes detected by identity evaluation.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes

/-- Cofibrations at every actual coefficient arrow. -/
def boundedFlatAffineSectionCof (R : CommRingCat.{u}) :
    MorphismProperty (BoundedFlatAffineSections R) := fun _ _ a =>
  ∀ j : Under R, (boundedFlatPerfectWaldhausen (Spec j.right)).cof
    ((boundedFlatAffineEvaluationAt R j).map a)

/-- Original weak equivalences at every actual coefficient arrow. -/
def boundedFlatAffineSectionWeq (R : CommRingCat.{u}) :
    MorphismProperty (BoundedFlatAffineSections R) := fun _ _ a =>
  ∀ j : Under R, (boundedFlatPerfectWaldhausen (Spec j.right)).weq
    ((boundedFlatAffineEvaluationAt R j).map a)

/-- Actual identity evaluation detects and preserves every pointwise cofibration. -/
theorem boundedFlatAffineSectionCof_iff (R : CommRingCat.{u})
    {s t : BoundedFlatAffineSections R} (a : s ⟶ t) :
    boundedFlatAffineSectionCof R a ↔
      (boundedFlatPerfectWaldhausen (Spec R)).cof
        ((boundedFlatAffineOriginalEvaluation R).map a) := by
  constructor
  · intro h
    have hh := h (Under.mk (𝟙 R))
    rw [boundedFlatAffineEvaluationAt_id] at hh
    exact hh
  · intro h j
    let e := boundedFlatAffineEvaluationPullbackIso R j
    have hm : (boundedFlatAffineEvaluationAt R j).map a =
        e.inv.app s ≫ (boundedFlatPerfectPullback (Spec.map j.hom)).map
          ((boundedFlatAffineOriginalEvaluation R).map a) ≫ e.hom.app t := by
      change (boundedFlatAffineEvaluationAt R j).map a = e.inv.app s ≫
        ((boundedFlatAffineOriginalEvaluation R ⋙
          boundedFlatPerfectPullback (Spec.map j.hom)).map a ≫ e.hom.app t)
      rw [e.hom.naturality]
      simp
    rw [hm]
    exact (boundedFlatPerfectWaldhausen (Spec j.right)).cof.comp_mem _ _
      ((boundedFlatPerfectWaldhausen (Spec j.right)).cof_iso _ inferInstance)
      ((boundedFlatPerfectWaldhausen (Spec j.right)).cof.comp_mem _ _
        ((boundedFlatPerfectPullback_exact (Spec.map j.hom)).cofibration _ h)
        ((boundedFlatPerfectWaldhausen (Spec j.right)).cof_iso _ inferInstance))

/-- Actual identity evaluation detects and preserves every pointwise weak equivalence. -/
theorem boundedFlatAffineSectionWeq_iff (R : CommRingCat.{u})
    {s t : BoundedFlatAffineSections R} (a : s ⟶ t) :
    boundedFlatAffineSectionWeq R a ↔
      (boundedFlatPerfectWaldhausen (Spec R)).weq
        ((boundedFlatAffineOriginalEvaluation R).map a) := by
  constructor
  · intro h
    have hh := h (Under.mk (𝟙 R))
    rw [boundedFlatAffineEvaluationAt_id] at hh
    exact hh
  · intro h j
    let e := boundedFlatAffineEvaluationPullbackIso R j
    have hm : (boundedFlatAffineEvaluationAt R j).map a =
        e.inv.app s ≫ (boundedFlatPerfectPullback (Spec.map j.hom)).map
          ((boundedFlatAffineOriginalEvaluation R).map a) ≫ e.hom.app t := by
      change (boundedFlatAffineEvaluationAt R j).map a = e.inv.app s ≫
        ((boundedFlatAffineOriginalEvaluation R ⋙
          boundedFlatPerfectPullback (Spec.map j.hom)).map a ≫ e.hom.app t)
      rw [e.hom.naturality]
      simp
    rw [hm]
    exact (boundedFlatPerfectWaldhausen (Spec j.right)).weq.comp_mem _ _
      ((boundedFlatPerfectWaldhausen (Spec j.right)).weq_iso _ inferInstance)
      ((boundedFlatPerfectWaldhausen (Spec j.right)).weq.comp_mem _ _
        ((boundedFlatPerfectPullback_exact (Spec.map j.hom)).weak _ h)
        ((boundedFlatPerfectWaldhausen (Spec j.right)).weq_iso _ inferInstance))

end Quillen.PerfectComplexes
