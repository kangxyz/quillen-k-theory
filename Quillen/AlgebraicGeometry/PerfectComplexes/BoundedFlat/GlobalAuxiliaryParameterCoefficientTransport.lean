/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalAuxiliaryParameterCoefficientRows

/-! # Original native support transport and the complete underlying comparison functors -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.GlobalAuxiliaryParameterCoefficient
open GlobalSectionChangeIndex

/-- Equality of actual native support opens transports Models without changing sections. -/
theorem nativeSupportTransport_forget {R : CommRingCat.{u}} (c : Index R)
    {A B : (space c).Opens} (h : A = B) :
    (eqToHom (congrArg (fun U : (space c).Opens =>
      boundedFlatCoefficientSupportedSectionModel (i := c) U.ι) h)).functor ⋙
        (boundedFlatCoefficientSectionSupported B.ι).ι =
      (boundedFlatCoefficientSectionSupported A.ι).ι := by
  cases h
  rfl

variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- The full fiber component retains the original ambient section comparison. -/
theorem fiberComponent_forget (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (fiberComponent f T a).functor ⋙
        (boundedFlatCoefficientSectionSupported
          (boundedFlatCoefficientFiberSupportOpen f T a).ι).ι =
      ((ParameterModels.forget (T ⊔ f.left.opensRange).ι).app (specUnder.obj a)).functor ⋙
        ((parameterCoefficientRestriction Q).app a).functor := by
  have ht := nativeSupportTransport_forget (op Q, a) (fiberSupportOpen_eq f T a).symm
  change (eqToHom (fiberModel_eq f T a)).functor ⋙
      (boundedFlatCoefficientSectionSupported
          (boundedFlatCoefficientFiberSupportOpen f T a).ι).ι =
    (boundedFlatCoefficientSectionSupported
      (boundedFlatCoefficientSupportOpen Q (T ⊔ f.left.opensRange) a).ι).ι at ht
  change (ambientComponent Q (T ⊔ f.left.opensRange) a).functor ⋙
    (eqToHom (fiberModel_eq f T a)).functor ⋙
      (boundedFlatCoefficientSectionSupported
          (boundedFlatCoefficientFiberSupportOpen f T a).ι).ι =
    ((ParameterModels.forget (T ⊔ f.left.opensRange).ι).app (specUnder.obj a)).functor ⋙
      ((parameterCoefficientRestriction Q).app a).functor
  rw [ht, ambientComponent_forget]

omit [IsOpenImmersion f.left] in
/-- The full-open component retains the original ambient section comparison on the open scheme. -/
theorem openComponent_forget (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (openComponent f T a).functor ⋙
        (boundedFlatCoefficientSectionSupported (boundedFlatCoefficientOpenSupportOpen f T a).ι).ι =
      ((ParameterModels.forget (f.left ⁻¹ᵁ T).ι).app (specUnder.obj a)).functor ⋙
        ((parameterCoefficientRestriction P).app a).functor := by
  have ht := nativeSupportTransport_forget (op P, a)
    (boundedFlatCoefficientOpenSupportOpen_eq f T a).symm
  change (eqToHom (openModel_eq f T a)).functor ⋙
      (boundedFlatCoefficientSectionSupported (boundedFlatCoefficientOpenSupportOpen f T a).ι).ι =
    (boundedFlatCoefficientSectionSupported
      (boundedFlatCoefficientSupportOpen P (f.left ⁻¹ᵁ T) a).ι).ι at ht
  change (ambientComponent P (f.left ⁻¹ᵁ T) a).functor ⋙
    (eqToHom (openModel_eq f T a)).functor ⋙
      (boundedFlatCoefficientSectionSupported (boundedFlatCoefficientOpenSupportOpen f T a).ι).ι =
    ((ParameterModels.forget (f.left ⁻¹ᵁ T).ι).app (specUnder.obj a)).functor ⋙
      ((parameterCoefficientRestriction P).app a).functor
  rw [ht, ambientComponent_forget]

end Quillen.PerfectComplexes.GlobalAuxiliaryParameterCoefficient
