/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalTensorUnitEvaluation

/-!
# Normalize genuine tensor multiplication by its whole functor unitor

The input is the original tensor functor and its actual structure-module automorphism.
Conjugation uses its entire natural unitor, and original fully faithful global evaluation
then lifts the resulting identity automorphism. No global tensor pseudofunctor is assumed.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.FunctorIdentityAutomorphism
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex

/-- Conjugate genuine tensor multiplication by the whole original tensor unitor. -/
def normalizedTensorUnit (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    𝟭 (BoundedFlatPerfect X) ≅ 𝟭 (BoundedFlatPerfect X) :=
  (boundedFlatPerfectTensorUnitIso X).symm ≪≫
    boundedFlatPerfectTensorUnitAutomorphism X r ≪≫ boundedFlatPerfectTensorUnitIso X

/-- The entire normalized tensor automorphism equals the original forward scalar. -/
theorem normalizedTensorUnit_eq (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    normalizedTensorUnit X r = boundedFlatPerfectGlobalUnitIso X r := by
  apply Iso.ext
  change (boundedFlatPerfectTensorUnitIso X).inv ≫
      (boundedFlatPerfectTensorUnitAutomorphism X r).hom ≫
        (boundedFlatPerfectTensorUnitIso X).hom = _
  rw [boundedFlatPerfectTensorUnitAutomorphism_unitor]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Lift the actual tensor-unitor conjugate through original fully faithful evaluation. -/
def globalNormalizedTensorUnit (X : Scheme.{u}ᵒᵖ) (r : (Γ(X.unop, ⊤))ˣ) :
    𝟭 (globalModel.obj X) ≅ 𝟭 (globalModel.obj X) :=
  lift (globalEvaluation X) (normalizedTensorUnit X.unop r)

/-- The lifted genuine tensor normalization is the existing original global unit. -/
theorem globalNormalizedTensorUnit_eq (X : Scheme.{u}ᵒᵖ) (r : (Γ(X.unop, ⊤))ˣ) :
    globalNormalizedTensorUnit X r = globalUnit X r := by
  unfold globalNormalizedTensorUnit
  rw [normalizedTensorUnit_eq]
  rfl

/-- Actual evaluation preserves the whole tensor-unitor normalized automorphism. -/
theorem globalNormalizedTensorUnit_evaluation (X : Scheme.{u}ᵒᵖ)
    (r : (Γ(X.unop, ⊤))ˣ) :
    Preserves (globalEvaluation X) (globalNormalizedTensorUnit X r)
      (normalizedTensorUnit X.unop r) :=
  map_lift_hom (globalEvaluation X) (normalizedTensorUnit X.unop r)

/-- Every scheme reindexing preserves this same normalized tensor action. -/
theorem globalNormalizedTensorUnit_reindex {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y)
    (r : (Γ(X.unop, ⊤))ˣ) :
    Preserves (globalModel.map f).functor (globalNormalizedTensorUnit X r)
      (globalNormalizedTensorUnit Y (Units.map f.unop.appTop.hom.toMonoidHom r)) := by
  rw [globalNormalizedTensorUnit_eq, globalNormalizedTensorUnit_eq]
  exact globalUnit_reindex f r

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
