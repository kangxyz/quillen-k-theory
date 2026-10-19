/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalTensorUnitEvaluation
public import Quillen.Waldhausen.SmallModel.Whiskering
public import Quillen.Aglib.CategoryTheory.Functor.IdentityAutomorphismRebase

/-! # Actual chosen-zero normalization of global evaluation -/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open Quillen.FunctorIdentityAutomorphism
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex

local instance (X : Scheme.{u}ᵒᵖ) :
    (AsSmall.down : SmallModel (BoundedFlatPerfect X.unop) ⥤
      BoundedFlatPerfect X.unop).IsEquivalence :=
  AsSmall.equiv.symm.isEquivalence_functor

/-- Original evaluation in the fixed common universe. -/
def evaluationSmall (X : Scheme.{u}ᵒᵖ) :
    globalModel.obj X ⥤ SmallModel (BoundedFlatPerfect X.unop) :=
  globalEvaluation X ⋙ AsSmall.up

/-- The unchanged evaluation and common-universe lift are exact. -/
theorem evaluationSmall_exact (X : Scheme.{u}ᵒᵖ) :
    IsExact (globalModel.obj X).waldhausen.cof (globalModel.obj X).waldhausen.weq
      (boundedFlatPerfectWaldhausen X.unop).smallModel.cof
      (boundedFlatPerfectWaldhausen X.unop).smallModel.weq (evaluationSmall X) :=
  (globalEvaluation_exact X).comp (boundedFlatPerfectWaldhausen X.unop).smallModel_up_exact

/-- The original evaluated zero has its unique comparison with the target chosen zero. -/
def evaluationZeroIso (X : Scheme.{u}ᵒᵖ) :
    (evaluationSmall X).obj (globalModel.obj X).waldhausen.zero ≅
      (boundedFlatPerfectWaldhausen X.unop).smallModel.zero :=
  ((evaluationSmall_exact X).zero (globalModel.obj X).waldhausen.isZero).iso
    (boundedFlatPerfectWaldhausen X.unop).smallModel.isZero

/-- Actual evaluation normalized only on its selected zero. -/
def evaluationModel (X : Scheme.{u}ᵒᵖ) :
    globalModel.obj X ⟶ modelOf (boundedFlatPerfectWaldhausen X.unop) where
  functor := Quillen.rebaseFunctor (evaluationSmall X) (globalModel.obj X).waldhausen.zero
    (boundedFlatPerfectWaldhausen X.unop).smallModel.zero (evaluationZeroIso X)
  exact := (evaluationSmall_exact X).rebase
  zero := Quillen.rebaseFunctor_obj_base _ _ _ _

/-- Retain the original complete normalization isomorphism. -/
def evaluationNormalizationIso (X : Scheme.{u}ᵒᵖ) :
    evaluationSmall X ≅ (evaluationModel X).functor :=
  Quillen.rebaseFunctorIso _ _ _ (evaluationZeroIso X)

/-- The original scalar identity automorphism in the common universe. -/
def evaluationSmallUnit (X : Scheme.{u}ᵒᵖ) (r : (Γ(X.unop, ⊤))ˣ) :
    𝟭 (SmallModel (BoundedFlatPerfect X.unop)) ≅
      𝟭 (SmallModel (BoundedFlatPerfect X.unop)) :=
  lift (AsSmall.down : SmallModel (BoundedFlatPerfect X.unop) ⥤ BoundedFlatPerfect X.unop)
    (boundedFlatPerfectGlobalUnitIso X.unop r)

/-- Universe lifting retains the evaluated original forward scalar. -/
theorem evaluationSmall_unit (X : Scheme.{u}ᵒᵖ) (r : (Γ(X.unop, ⊤))ˣ) :
    Preserves (evaluationSmall X) (globalUnit X r) (evaluationSmallUnit X r) := by
  intro S
  apply (AsSmall.down : SmallModel (BoundedFlatPerfect X.unop) ⥤
    BoundedFlatPerfect X.unop).map_injective
  change (globalEvaluation X).map ((globalUnit X r).hom.app S) =
    AsSmall.down.map ((evaluationSmallUnit X r).hom.app
      (AsSmall.up.obj ((globalEvaluation X).obj S)))
  rw [evaluationSmallUnit, map_lift_hom]
  exact globalUnit_evaluation X r S

/-- Actual zero normalization preserves the same original unit, without a new choice. -/
theorem evaluationModel_unit (X : Scheme.{u}ᵒᵖ) (r : (Γ(X.unop, ⊤))ˣ) :
    Preserves (evaluationModel X).functor (globalUnit X r) (evaluationSmallUnit X r) :=
  rebase_preserves _ _ _ _ _ _ (evaluationSmall_unit X r)

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
