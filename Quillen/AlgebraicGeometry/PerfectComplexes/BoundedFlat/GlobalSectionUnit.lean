/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSectionChangeIndexLaws
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.CoefficientSectionUnits
public import Quillen.Aglib.CategoryTheory.Functor.IdentityAutomorphismEvaluation

/-! # Original scalar units on global sections and their actual restriction -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.CategoryTheory.GrothendieckSections
open Quillen.FunctorIdentityAutomorphism
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex

/-- Original global evaluation with its actual Model-category source made explicit. -/
def globalEvaluation (X : Scheme.{u}ᵒᵖ) :
    globalModel.obj X ⥤ BoundedFlatPerfect X.unop :=
  originalEvaluation boundedFlatPerfectPseudofunctor X

instance globalEvaluation_isEquivalence (X : Scheme.{u}ᵒᵖ) :
    (globalEvaluation X).IsEquivalence :=
  inferInstanceAs (originalEvaluation boundedFlatPerfectPseudofunctor X).IsEquivalence

/-- The original geometric scalar lifted through original identity evaluation. -/
def globalUnit (X : Scheme.{u}ᵒᵖ) (r : (Γ(X.unop, ⊤))ˣ) :
    𝟭 (globalModel.obj X) ≅ 𝟭 (globalModel.obj X) :=
  lift (globalEvaluation X)
    (boundedFlatPerfectGlobalUnitIso X.unop r)

/-- Evaluation keeps every original scalar component literally. -/
theorem globalUnit_evaluation (X : Scheme.{u}ᵒᵖ) (r : (Γ(X.unop, ⊤))ˣ) :
    Preserves (globalEvaluation X)
      (globalUnit X r) (boundedFlatPerfectGlobalUnitIso X.unop r) :=
  map_lift_hom (globalEvaluation X) (boundedFlatPerfectGlobalUnitIso X.unop r)

/-- Original scheme reindexing preserves the actual pulled-back scalar unit. -/
theorem globalUnit_reindex {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y)
    (r : (Γ(X.unop, ⊤))ˣ) :
    Preserves (globalModel.map f).functor (globalUnit X r)
      (globalUnit Y (Units.map f.unop.appTop.hom.toMonoidHom r)) := by
  let e := (originalEvaluationTransitionIso boundedFlatPerfectPseudofunctor X
    (Under.mk f)) ≪≫
    eqToIso (originalEvaluation_reindex boundedFlatPerfectPseudofunctor X f).symm
  intro S
  apply (globalEvaluation Y).map_injective
  have h := map_hom_eq_of_iso _ _ e.symm (globalUnit X r)
    (boundedFlatPerfectGlobalUnitIso Y.unop
      (Units.map f.unop.appTop.hom.toMonoidHom r)) (fun T => by
        change (boundedFlatPerfectPullback f.unop).map
          ((globalEvaluation X).map
            ((globalUnit X r).hom.app T)) = _
        rw [globalUnit_evaluation, boundedFlatPerfectPullback_map_globalUnit]
        rfl) S
  exact h.trans (globalUnit_evaluation Y _ ((globalModel.map f).functor.obj S)).symm

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
