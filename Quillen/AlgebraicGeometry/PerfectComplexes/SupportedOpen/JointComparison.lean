/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.Fibration.Rows.OppositeComplexJointMap
public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.Restriction

/-! # Original supported restriction intertwines the actual common cocylinders -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Quillen.PerfectComplexes
open Waldhausen Fibration
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

/-- The literal original corestriction preserves the actual common opposite cocylinder. -/
def perfectSupportedRestrictOpJointIso :
    (perfectSupportedOppositeJointData T.ι).joint ⋙
      ExtensionCategory.postcompose (perfectSupportedOppositeWaldhausen T.ι)
        (perfectSupportedOppositeWaldhausen (j ⁻¹ᵁ T).ι)
        (perfectSupportedRestrict_op_exact j T) ≅
      (perfectSupportedRestrict j T).op.mapArrow ⋙ (perfectSupportedOppositeJointData (j ⁻¹ᵁ
        T).ι).joint :=
  oppositeComplexJointDataMapIso (Scheme.Modules.restrictFunctor j)
    (perfectSupported T.ι) (perfectSupported (j ⁻¹ᵁ T).ι) (fun _ hK => perfectSupported_restrict j T
      hK)
    (fun _ h => perfectSupported_shift T.ι h (-1))
    (fun _ h => perfectSupported_shift (j ⁻¹ᵁ T).ι h (-1))
    (perfectSupportedRestrict_op_exact j T)

lemma perfectSupportedRestrictOpJointIso_inv_inl (f : Arrow (perfectSupported
  T.ι).FullSubcategoryᵒᵖ) :
    (perfectSupportedOppositeJointData (j ⁻¹ᵁ T).ι).inl.app ((perfectSupportedRestrict j
      T).op.mapArrow.obj f) ≫
        ((perfectSupportedRestrictOpJointIso j T).inv.app f).hom.left =
      (perfectSupportedRestrict j T).op.map ((perfectSupportedOppositeJointData T.ι).inl.app f) :=
  oppositeComplexJointDataMapIso_inv_inl _ _ _ _ _ _ _ f

lemma perfectSupportedRestrictOpJointIso_inv_inr (f : Arrow (perfectSupported
  T.ι).FullSubcategoryᵒᵖ) :
    (perfectSupportedOppositeJointData (j ⁻¹ᵁ T).ι).inr.app ((perfectSupportedRestrict j
      T).op.mapArrow.obj f) ≫
        ((perfectSupportedRestrictOpJointIso j T).inv.app f).hom.left =
      (perfectSupportedRestrict j T).op.map ((perfectSupportedOppositeJointData T.ι).inr.app f) :=
  oppositeComplexJointDataMapIso_inv_inr _ _ _ _ _ _ _ f

lemma perfectSupportedRestrictOpJointIso_inv_projection (f : Arrow (perfectSupported
  T.ι).FullSubcategoryᵒᵖ) :
    ((perfectSupportedRestrictOpJointIso j T).inv.app f).hom.right ≫
        (perfectSupportedRestrict j T).op.map ((perfectSupportedOppositeJointData
          T.ι).projection.app f) =
      (perfectSupportedOppositeJointData (j ⁻¹ᵁ T).ι).projection.app ((perfectSupportedRestrict j
        T).op.mapArrow.obj f) :=
  oppositeComplexJointDataMapIso_inv_projection _ _ _ _ _ _ _ f

end Quillen.PerfectComplexes
