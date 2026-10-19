/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedInputNormalization

/-! # The independent supported tensor action through the original forgetful functor

The supported action is the original full-subcategory lift. Its genuine comparison
with ambient tensor preserves the forward unit automorphism before normalization.
The resulting exact-functor square produces a whole spectrum prism.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The actual ambient tensor functor is exact by its original left unitor. -/
theorem tensorCoefficientAmbientTensor_exact :
    IsExact (boundedFlatPerfectWaldhausen X).cof (boundedFlatPerfectWaldhausen X).weq
      (boundedFlatPerfectWaldhausen X).cof (boundedFlatPerfectWaldhausen X).weq
      (boundedFlatPerfectTensorUnit X) :=
  (IsExact.id _ _).of_iso (boundedFlatPerfectTensorUnitIso X).symm

/-- Forgetting the original support commutes with tensor through its genuine underlying iso. -/
def tensorSupportedForgetIso :
    boundedFlatPerfectSupportedTensorUnit j ⋙ tensorCoefficientSupportedForget j ≅
      tensorCoefficientSupportedForget j ⋙ boundedFlatPerfectTensorUnit X :=
  NatIso.ofComponents (fun _ => Iso.refl _)
    (by intro A B g; simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)

/-- The original supported forward unit agrees with the actual ambient tensor coefficient. -/
theorem tensorSupportedForget_unit (r : (Γ(X, ⊤))ˣ) :
    Functor.whiskerRight (boundedFlatPerfectSupportedTensorUnitAutomorphism j r).hom
        (tensorCoefficientSupportedForget j) ≫ (tensorSupportedForgetIso j).hom =
      (tensorSupportedForgetIso j).hom ≫
        Functor.whiskerLeft (tensorCoefficientSupportedForget j)
          (boundedFlatPerfectTensorUnitAutomorphism X r).hom := by
  apply NatTrans.ext
  funext K
  apply (boundedFlatPerfect X).ι.map_injective
  simp only [NatTrans.comp_app, tensorSupportedForgetIso,
    NatIso.ofComponents_hom_app, Iso.refl_hom,
    Category.id_comp, Category.comp_id, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  exact (boundedFlatPerfectSupportedTensorUnitAutomorphism_hom_original j r K).trans
    (boundedFlatPerfectTensorUnitAutomorphism_hom_original X r
      ((tensorCoefficientSupportedForget j).obj K)).symm

/-- Whole normalized spectrum pastings retain the independent supported/ambient tensor square. -/
def tensorSupportedForgetPasting (r : (Γ(X, ⊤))ˣ) :=
  exactOriginalPrespectrumPastingHomotopy
    (boundedFlatPerfectSupportedWaldhausen j) (boundedFlatPerfectWaldhausen X)
    ((boundedFlatPerfectSupportedTensorUnit_exact j).comp
      (tensorCoefficientSupportedForget_exact j))
    ((boundedFlatPerfectSupportedTensorUnit_exact j).comp
      (tensorCoefficientSupportedForget_exact j))
    ((tensorCoefficientSupportedForget_exact j).comp (tensorCoefficientAmbientTensor_exact))
    ((tensorCoefficientSupportedForget_exact j).comp (tensorCoefficientAmbientTensor_exact))
    (Functor.whiskerRight (boundedFlatPerfectSupportedTensorUnitAutomorphism j r).hom
      (tensorCoefficientSupportedForget j))
    (tensorSupportedForgetIso j).hom (tensorSupportedForgetIso j).hom
    (Functor.whiskerLeft (tensorCoefficientSupportedForget j)
      (boundedFlatPerfectTensorUnitAutomorphism X r).hom)
    (fun _ => (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
    (fun _ => (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
    (fun _ => (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
    (fun _ => (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
    (tensorSupportedForget_unit j r)

end Quillen.PerfectComplexes
