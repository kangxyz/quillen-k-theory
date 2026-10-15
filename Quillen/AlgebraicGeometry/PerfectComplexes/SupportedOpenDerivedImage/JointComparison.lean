/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.Fibration.Rows.OppositeComplexJointMap
public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpenDerivedImage.Structure

/-!
# Original restriction cocylinders in the derived-saturated image

The actual exact open restriction, with its literal derived-image witness,
intertwines the original common opposite cocylinders. The natural isomorphism
retains the exact first endpoint, second endpoint and projection equations.
The target image structures use the explicit genuine derived-roof property;
no approximation or localization conclusion is assumed here.
-/
@[expose] public section

open Quillen.Waldhausen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Quillen.PerfectComplexes.SupportedOpenDerivedImage
open Waldhausen Fibration
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens) [Fact
  (OpenDerivedImage.HasSupportedDerivedRoofs j T)]

/-- The literal original corestriction preserves the actual common opposite cocylinder. -/
def complexCorestrictOpJointIso :
    (perfectSupportedOppositeJointData T.ι).joint ⋙
      ExtensionCategory.postcompose (perfectSupportedOppositeWaldhausen T.ι)
        (complexOppositeWaldhausen j T)
        (complexCorestrict_op_exact j T) ≅
      (complexCorestrict j T).op.mapArrow ⋙ (complexOppositeJointData j T).joint :=
  oppositeComplexJointDataMapIso (Scheme.Modules.restrictFunctor j)
    (perfectSupported T.ι) (complexObjects j T) (fun K hK => ⟨K, hK, ⟨Iso.refl _⟩⟩)
    (fun _ h => perfectSupported_shift T.ι h (-1)) (fun _ h => complexObjects_shift j T h (-1))
    (complexCorestrict_op_exact j T)

lemma complexCorestrictOpJointIso_inv_inl (f : Arrow (perfectSupported T.ι).FullSubcategoryᵒᵖ) :
    (complexOppositeJointData j T).inl.app ((complexCorestrict j T).op.mapArrow.obj f) ≫
        ((complexCorestrictOpJointIso j T).inv.app f).hom.left =
      (complexCorestrict j T).op.map ((perfectSupportedOppositeJointData T.ι).inl.app f) :=
  oppositeComplexJointDataMapIso_inv_inl _ _ _ _ _ _ _ f

lemma complexCorestrictOpJointIso_inv_inr (f : Arrow (perfectSupported T.ι).FullSubcategoryᵒᵖ) :
    (complexOppositeJointData j T).inr.app ((complexCorestrict j T).op.mapArrow.obj f) ≫
        ((complexCorestrictOpJointIso j T).inv.app f).hom.left =
      (complexCorestrict j T).op.map ((perfectSupportedOppositeJointData T.ι).inr.app f) :=
  oppositeComplexJointDataMapIso_inv_inr _ _ _ _ _ _ _ f

lemma complexCorestrictOpJointIso_inv_projection (f : Arrow (perfectSupported
  T.ι).FullSubcategoryᵒᵖ) :
    ((complexCorestrictOpJointIso j T).inv.app f).hom.right ≫
        (complexCorestrict j T).op.map ((perfectSupportedOppositeJointData T.ι).projection.app f) =
      (complexOppositeJointData j T).projection.app ((complexCorestrict j T).op.mapArrow.obj f) :=
  oppositeComplexJointDataMapIso_inv_projection _ _ _ _ _ _ _ f

end Quillen.PerfectComplexes.SupportedOpenDerivedImage
