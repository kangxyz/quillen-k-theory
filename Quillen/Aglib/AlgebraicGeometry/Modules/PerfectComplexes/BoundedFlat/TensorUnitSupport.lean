/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.TensorUnitAction
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.Support

/-!
# The actual tensor-unit action with original acyclic support

The original support property is acyclicity after restriction to the specified open. The actual
tensor left unitor preserves that property and restricts the tensor/scalar square to the full
supported category, without changing any underlying complex or chain map.

Intended upstream owner:
`Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.TensorUnitSupport`.
The hypotheses are an arbitrary scheme and an actual open immersion. The current consumer is
the restricted tensor-unit iterated-S comparison in Quillen.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Complex
universe u
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Actual acyclicity after the original open restriction is preserved by unit tensor. -/
theorem boundedFlatPerfectTensorUnit_supported {K : CochainComplex X.Modules ℤ}
    (hK : boundedFlatPerfectSupported j K) :
    boundedFlatPerfectSupported j
      ((tensorLeft (SheafOfModules.unit X.ringCatSheaf)).obj K) :=
  (boundedFlatPerfectSupported j).prop_of_iso ((complexTensorUnitIso X).app K).symm hK

/-- Genuine structure-module tensor on the original supported full subcategory. -/
def boundedFlatPerfectSupportedTensorUnit :
    (boundedFlatPerfectSupported j).FullSubcategory ⥤
      (boundedFlatPerfectSupported j).FullSubcategory :=
  (boundedFlatPerfectSupported j).lift
    ((boundedFlatPerfectSupported j).ι ⋙ tensorLeft (SheafOfModules.unit X.ringCatSheaf))
    (fun K ↦ boundedFlatPerfectTensorUnit_supported j K.property)

/-- The original tensor unitor restricted to the acyclic-support category. -/
def boundedFlatPerfectSupportedTensorUnitIso :
    boundedFlatPerfectSupportedTensorUnit j ≅ 𝟭 (boundedFlatPerfectSupported j).FullSubcategory :=
  Functor.fullyFaithfulCancelRight (boundedFlatPerfectSupported j).ι
    (Functor.isoWhiskerLeft (boundedFlatPerfectSupported j).ι (complexTensorUnitIso X))

/-- The unchanged structure-module coefficient action on supported complexes. -/
def boundedFlatPerfectSupportedTensorUnitAutomorphism (r : (Γ(X, ⊤))ˣ) :
    boundedFlatPerfectSupportedTensorUnit j ≅ boundedFlatPerfectSupportedTensorUnit j :=
  Functor.fullyFaithfulCancelRight (boundedFlatPerfectSupported j).ι
    (Functor.isoWhiskerLeft (boundedFlatPerfectSupported j).ι (complexTensorUnitAutomorphism X r))

/-- Restrict the existing forward scalar automorphism to actual supported complexes. -/
def boundedFlatPerfectSupportedGlobalUnitIso (r : (Γ(X, ⊤))ˣ) :
    𝟭 (boundedFlatPerfectSupported j).FullSubcategory ≅
      𝟭 (boundedFlatPerfectSupported j).FullSubcategory :=
  Functor.fullyFaithfulCancelRight (boundedFlatPerfectSupported j).ι
    (Functor.isoWhiskerLeft (boundedFlatPerfectSupported j).ι (complexGlobalUnitIso X r))

/-- Forgetting support retains the original coefficient tensor map on the underlying complex. -/
theorem boundedFlatPerfectSupportedTensorUnitAutomorphism_hom_original
    (r : (Γ(X, ⊤))ˣ) (K : (boundedFlatPerfectSupported j).FullSubcategory) :
    (boundedFlatPerfectSupported j).ι.map
        ((boundedFlatPerfectSupportedTensorUnitAutomorphism j r).hom.app K) =
      (complexTensorUnitAutomorphism X r).hom.app K.obj := by
  simp only [boundedFlatPerfectSupportedTensorUnitAutomorphism,
    Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, ObjectProperty.ι_obj]

/-- The whole actual tensor/scalar square restricts to original supported complexes. -/
theorem boundedFlatPerfectSupportedTensorUnitAutomorphism_unitor (r : (Γ(X, ⊤))ˣ) :
    (boundedFlatPerfectSupportedTensorUnitAutomorphism j r).hom ≫
        (boundedFlatPerfectSupportedTensorUnitIso j).hom =
      (boundedFlatPerfectSupportedTensorUnitIso j).hom ≫
        (boundedFlatPerfectSupportedGlobalUnitIso j r).hom := by
  apply NatTrans.ext
  funext K
  apply (boundedFlatPerfectSupported j).ι.map_injective
  simp only [NatTrans.comp_app, Functor.map_comp,
    boundedFlatPerfectSupportedTensorUnitAutomorphism_hom_original,
    boundedFlatPerfectSupportedTensorUnitIso, boundedFlatPerfectSupportedGlobalUnitIso,
    Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, ObjectProperty.ι_obj]
  exact NatTrans.congr_app (complexTensorUnitAutomorphism_unitor X r) K.obj

end Quillen.PerfectComplexes
