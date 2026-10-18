/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedSections
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportLocalizationModels

/-!
# Supported global Models and their actual restriction square

The supported full subcategory retains the global chosen zero. Its original evaluation
transports the geometric supported Waldhausen structure. Restriction and forgetting support
are actual exact zero-preserving Model arrows, and their square commutes strictly.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Complex
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex

/-- The unchanged original global evaluation is Waldhausen-exact. -/
theorem globalEvaluation_exact (X : Scheme.{u}ᵒᵖ) :
    IsExact (globalModel.obj X).waldhausen.cof (globalModel.obj X).waldhausen.weq
      (boundedFlatPerfectWaldhausen X.unop).cof (boundedFlatPerfectWaldhausen X.unop).weq
      (globalEvaluation X) :=
  Quillen.Waldhausen.IteratedS.SectionChangeIndexMixedModel.evaluation_exact
    boundedFlatPerfectPseudofunctor fiberWaldhausen fiberZero fiberZero_isZero
    (fun {_ _} f => fiberZero_map_isZero f) X

variable {X : Scheme.{u}ᵒᵖ} {U : Scheme.{u}} (j : U ⟶ X.unop) [IsOpenImmersion j]

/-- The original global chosen zero satisfies actual support on every open. -/
theorem globalZero_supported : supported j (globalModel.obj X).waldhausen.zero :=
  HomologicalComplex.acyclic_of_isZero _ ((restrict j).map_isZero
    ((boundedFlatPerfect X.unop).ι.map_isZero
      ((globalEvaluation_exact X).zero (globalModel.obj X).waldhausen.isZero)))

/-- The supported zero keeps the original global section literally. -/
def supportedZero : (supported j).FullSubcategory :=
  ⟨(globalModel.obj X).waldhausen.zero, globalZero_supported j⟩

/-- Original supported evaluation sends this unchanged chosen zero to zero. -/
theorem supportedZero_evaluation_isZero :
    IsZero ((supportedEvaluation j).obj (supportedZero j)) :=
  IsZero.of_full_of_faithful_of_isZero (boundedFlatPerfectSupported j).ι _
    ((boundedFlatPerfect X.unop).ι.map_isZero
      ((globalEvaluation_exact X).zero (globalModel.obj X).waldhausen.isZero))

/-- Original supported classes with the actual restricted global zero. -/
def supportedWaldhausen : Structure (supported j).FullSubcategory :=
  (boundedFlatPerfectSupportedWaldhausen j).ofEquivalence
    (supportedEvaluation j).asEquivalence (supportedZero j)
    (supportedZero_evaluation_isZero j)

/-- The actual global supported Model. -/
def supportedModel : Model.{u+1} :=
  ⟨Cat.of (supported j).FullSubcategory, supportedWaldhausen j⟩

/-- Supported evaluation is exact for the unchanged geometric classes. -/
theorem supportedEvaluation_exact :
    IsExact (supportedWaldhausen j).cof (supportedWaldhausen j).weq
      (boundedFlatPerfectSupportedWaldhausen j).cof
      (boundedFlatPerfectSupportedWaldhausen j).weq (supportedEvaluation j) :=
  Structure.ofEquivalence_exact _ _ _ _

/-- Supported evaluation commutes with the actual geometric inclusion. -/
theorem supportedEvaluation_forget :
    supportedEvaluation j ⋙ ObjectProperty.ιOfLE
      (show boundedFlatPerfectSupported j ≤ boundedFlatPerfect X.unop from fun _ h => h.1) =
      (supported j).ι ⋙ globalEvaluation X := by
  unfold supportedEvaluation
  exact Quillen.ObjectProperty.lift_comp_ιOfLE_comp
    (boundedFlatPerfectSupported j) (boundedFlatPerfect X.unop)
    (fun _ h => h.1) (supported j).ι (globalEvaluation X)
    (fun S => ⟨((globalEvaluation X).obj S.obj).property, S.property⟩)

/-- Forgetting support is exact after original evaluation. -/
theorem supportedForget_evaluation_exact :
    IsExact (supportedWaldhausen j).cof (supportedWaldhausen j).weq
      (boundedFlatPerfectWaldhausen X.unop).cof
      (boundedFlatPerfectWaldhausen X.unop).weq
      ((supported j).ι ⋙ globalEvaluation X) := by
  rw [← supportedEvaluation_forget j]
  exact (supportedEvaluation_exact j).comp
    (subcategoryInclusion_exact _ _ (fun _ h => h.1))

/-- Forgetting support is exact for the original global structure. -/
theorem supportedForget_exact :
    IsExact (supportedWaldhausen j).cof (supportedWaldhausen j).weq
      (globalModel.obj X).waldhausen.cof (globalModel.obj X).waldhausen.weq
      (supported j).ι where
  zero hz := IsZero.of_full_of_faithful_of_isZero (globalEvaluation X) _
    ((supportedForget_evaluation_exact j).zero hz)
  cofibration f hf := (supportedForget_evaluation_exact j).cofibration f hf
  weak f hf := (supportedForget_evaluation_exact j).weak f hf
  pushout hi hp := IsPushout.of_map_of_faithful (globalEvaluation X)
    ((supportedForget_evaluation_exact j).pushout hi hp)

/-- Forgetting support preserves the actual global zero literally. -/
def supportedForget : supportedModel j ⟶ globalModel.obj X where
  functor := (supported j).ι
  exact := supportedForget_exact j
  zero := rfl

variable (R : CommRingCat.{u}) (c : Index R) {V : Scheme.{u}}
    (k : V ⟶ space c) [IsOpenImmersion k]

/-- Restriction is a categorical equivalence on the actual supported subcategories. -/
instance supportedRestriction_isEquivalence : (supportedRestriction R c k).IsEquivalence := by
  let : (supportedRestriction R c k ⋙
      boundedFlatCoefficientSupportedEvaluation k).IsEquivalence := by
    rw [supportedRestriction_evaluation]
    exact supportedEvaluation_isEquivalence (X :=
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj c) k
  exact CategoryTheory.Functor.isEquivalence_of_comp_right
    (supportedRestriction R c k) (boundedFlatCoefficientSupportedEvaluation k)

/-- Supported coefficient restriction is exact by its complete evaluation square. -/
theorem supportedRestriction_exact :
    IsExact (supportedWaldhausen (X :=
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj c) k).cof
      (supportedWaldhausen (X :=
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj c) k).weq
      (boundedFlatCoefficientSupportedSectionWaldhausen k).cof
      (boundedFlatCoefficientSupportedSectionWaldhausen k).weq
      (supportedRestriction R c k) := by
  have he : IsExact (supportedWaldhausen (X :=
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj c) k).cof
      (supportedWaldhausen (X :=
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj c) k).weq
      (boundedFlatPerfectSupportedWaldhausen k).cof
      (boundedFlatPerfectSupportedWaldhausen k).weq
      (supportedRestriction R c k ⋙ boundedFlatCoefficientSupportedEvaluation k) := by
    rw [supportedRestriction_evaluation]
    exact supportedEvaluation_exact (X :=
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj c) k
  exact {
    zero := fun hz => IsZero.of_full_of_faithful_of_isZero
      (boundedFlatCoefficientSupportedEvaluation k) _ (he.zero hz)
    cofibration := fun f hf => he.cofibration f hf
    weak := fun f hf => he.weak f hf
    pushout := fun hi hp => IsPushout.of_map_of_faithful
      (boundedFlatCoefficientSupportedEvaluation k) (he.pushout hi hp) }

/-- The actual supported restriction is a strictly zero-preserving Model map. -/
def supportedRestrictionModel : supportedModel
    (X := (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj c) k ⟶
    boundedFlatCoefficientSupportedSectionModel k where
  functor := supportedRestriction R c k
  exact := supportedRestriction_exact R c k
  zero := by
    apply ObjectProperty.FullSubcategory.ext
    exact ((coefficientRestriction R).app c).zero

/-- Actual supported restriction and forgetting support commute as Model arrows. -/
theorem supportedRestrictionModel_forget
    {P Q : Over (Spec R)} (f : P ⟶ Q) [IsOpenImmersion f.left] (a : Under R) :
    supportedRestrictionModel R (Opposite.op Q, a) (schemeMap f a) ≫
        boundedFlatCoefficientSupportedForgetModelMap f a =
      supportedForget (X := (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj
        (Opposite.op Q, a)) (schemeMap f a) ≫
        (coefficientRestriction R).app (Opposite.op Q, a) := by
  apply Model.Hom.ext
  exact supportedRestriction_forget R (Opposite.op Q, a) (schemeMap f a)

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
