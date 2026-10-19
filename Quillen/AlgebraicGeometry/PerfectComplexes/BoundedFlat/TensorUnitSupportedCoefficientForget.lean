/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedCoefficientAutomorphism
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedForgetNaturality

/-!
# Forgetting the independently constructed supported first tensor row

The genuine supported row has already been constructed internally. Its exact forgetful image
retains the original ambient tensor row and every coefficient multiplication entry.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.QuotientRows
open scoped Simplicial
universe u
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} (ι : U ⟶ X) [IsOpenImmersion ι]

/-- The actual supported first row forgets to the independently constructed ambient row. -/
def supportedTensorUnitFirstRowForgetIso :
    boundedFlatPerfectSupportedTensorUnitFirstRow ι ⋙
      postcompose (boundedFlatPerfectSupportedWaldhausen ι) (boundedFlatPerfectWaldhausen X)
        (tensorCoefficientSupportedForget_exact ι) ⦋1⦌ ≅
      tensorCoefficientSupportedForget ι ⋙ boundedFlatPerfectTensorUnitFirstRow X :=
  NatIso.ofComponents (fun K => (objects (boundedFlatPerfectWaldhausen X) ⦋1⦌).isoMk
    (NatIso.ofComponents (fun _ => Iso.refl _) (by
      intro p q f
      simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
      rfl))) (by
    intro K L f
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext p
    change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
    rw [Category.comp_id, Category.id_comp]
    rfl)

/-- The whole supported coefficient multiplication has the same exact forgetful image. -/
theorem supportedTensorUnitFirstRowForget_unit (r : (Γ(X, ⊤))ˣ) :
    Functor.whiskerRight (supportedTensorUnitFirstRowAutomorphism ι r).hom
        (postcompose (boundedFlatPerfectSupportedWaldhausen ι) (boundedFlatPerfectWaldhausen X)
          (tensorCoefficientSupportedForget_exact ι) ⦋1⦌) ≫
        (supportedTensorUnitFirstRowForgetIso ι).hom =
      (supportedTensorUnitFirstRowForgetIso ι).hom ≫
        Functor.whiskerLeft (tensorCoefficientSupportedForget ι)
          (tensorUnitFirstRowAutomorphism X r).hom := by
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext p
  change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
  rw [Category.comp_id, Category.id_comp]
  change (tensorCoefficientSupportedForget ι).map
      (((supportedTensorUnitFirstRowAutomorphism ι r).hom.app K).hom.app p) =
    (((tensorUnitFirstRowAutomorphism X r).hom.app
      ((tensorCoefficientSupportedForget ι).obj K)).hom.app p)
  rw [tensorUnitFirstRowAutomorphism_original,
    supportedTensorUnitFirstRowAutomorphism_original]
  apply (boundedFlatPerfect X).ι.map_injective
  ext n : 1
  change ((boundedFlatPerfectSupported ι).ι.map
      (((boundedFlatPerfectSupportedTensorUnitRowsAutomorphism ι r).hom.app K).app p)).f n = _
  rw [supportedTensorUnitRowsAutomorphism_original_f, tensorUnitRowsAutomorphism_original_f]
  rfl

end Quillen.PerfectComplexes
