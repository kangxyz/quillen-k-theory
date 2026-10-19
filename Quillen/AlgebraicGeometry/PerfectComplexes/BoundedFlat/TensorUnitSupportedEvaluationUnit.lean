/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedEvaluationModel
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalEvaluationModel
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportHomotopy

/-! # The original supported scalar through actual evaluation and selected-zero transport -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.FunctorIdentityAutomorphism
universe u
namespace Quillen.PerfectComplexes.SupportedTensorEvaluation
open GlobalSectionChangeIndex
variable {X : Scheme.{u}ᵒᵖ} {U : Scheme.{u}} (j : U ⟶ X.unop) [IsOpenImmersion j]

/-- The same global scalar restricted to actual supported sections. -/
def unit (r : (Γ(X.unop, ⊤))ˣ) :
    𝟭 (supported j).FullSubcategory ≅ 𝟭 (supported j).FullSubcategory :=
  lift (supported j).ι (globalUnit X r)

/-- Actual evaluation preserves the original supported scalar componentwise. -/
theorem evaluation_unit (r : (Γ(X.unop, ⊤))ˣ) :
    Preserves (supportedEvaluation j) (unit j r)
      (boundedFlatPerfectSupportedGlobalUnitIso j r) := by
  intro K
  apply (boundedFlatPerfectSupported j).ι.map_injective
  change (boundedFlatPerfect X.unop).ι.map
      ((globalEvaluation X).map ((supported j).ι.map ((unit j r).hom.app K))) = _
  rw [unit, map_lift_hom, globalUnit_evaluation]
  simp only [boundedFlatPerfectSupportedGlobalUnitIso, boundedFlatPerfectGlobalUnitIso,
    Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, ObjectProperty.ι_obj]
  rfl

local instance :
    (AsSmall.down : SmallModel ((boundedFlatPerfectSupported j).FullSubcategory) ⥤
      (boundedFlatPerfectSupported j).FullSubcategory).IsEquivalence :=
  AsSmall.equiv.symm.isEquivalence_functor

/-- The original supported scalar in the fixed common universe. -/
def smallUnit (r : (Γ(X.unop, ⊤))ˣ) :
    𝟭 (SmallModel ((boundedFlatPerfectSupported j).FullSubcategory)) ≅
      𝟭 (SmallModel ((boundedFlatPerfectSupported j).FullSubcategory)) :=
  lift (AsSmall.down : SmallModel ((boundedFlatPerfectSupported j).FullSubcategory) ⥤
    (boundedFlatPerfectSupported j).FullSubcategory)
    (boundedFlatPerfectSupportedGlobalUnitIso j r)

/-- Universe transport retains the entire evaluated scalar. -/
theorem evaluationSmall_unit (r : (Γ(X.unop, ⊤))ˣ) :
    Preserves (evaluationSmall j) (unit j r) (smallUnit j r) := by
  intro K
  apply (AsSmall.down : SmallModel ((boundedFlatPerfectSupported j).FullSubcategory) ⥤
    (boundedFlatPerfectSupported j).FullSubcategory).map_injective
  change (supportedEvaluation j).map ((unit j r).hom.app K) =
    AsSmall.down.map ((smallUnit j r).hom.app
      (AsSmall.up.obj ((supportedEvaluation j).obj K)))
  rw [smallUnit, map_lift_hom]
  exact evaluation_unit j r K

/-- Actual chosen-zero normalization preserves this same supported unit. -/
theorem evaluationModel_unit (r : (Γ(X.unop, ⊤))ˣ) :
    Preserves (evaluationModel j).functor (unit j r) (smallUnit j r) :=
  rebase_preserves _ _ _ _ _ _ (evaluationSmall_unit j r)

end Quillen.PerfectComplexes.SupportedTensorEvaluation
