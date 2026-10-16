/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.Fibration.Rows.OppositeComplexJointMap
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.Structure
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalClosure

/-!
# Original restriction cocylinders in the derived-saturated image

The actual exact open restriction, with its literal derived-image witness,
intertwines the original common opposite cocylinders. The natural isomorphism
retains the exact first endpoint, second endpoint and projection equations.
The target image structures use the explicit genuine derived-roof property;
no approximation or localization conclusion is assumed here.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open Quillen.Waldhausen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Quillen.PerfectComplexes.OpenDerivedImage
open Waldhausen Fibration
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [Fact (HasDerivedRoofs j)]

/-- The literal original corestriction preserves the actual common opposite cocylinder. -/
def complexCorestrictOpJointIso :
    (perfectOppositeJointData X).joint ⋙
      ExtensionCategory.postcompose (perfectOppositeWaldhausen X) (complexOppositeWaldhausen j)
        (complexCorestrict_op_exact j) ≅
      (complexCorestrict j).op.mapArrow ⋙ (complexOppositeJointData j).joint :=
  oppositeComplexJointDataMapIso (Scheme.Modules.restrictFunctor j)
    (locallyPerfect X) (complexObjects j) (fun K hK => ⟨K, hK, ⟨Iso.refl _⟩⟩)
    (fun _ h => locallyPerfect_shift h (-1)) (fun _ h => complexObjects_shift j h (-1))
    (complexCorestrict_op_exact j)

lemma complexCorestrictOpJointIso_inv_inl (f : Arrow (Perfect X)ᵒᵖ) :
    (complexOppositeJointData j).inl.app ((complexCorestrict j).op.mapArrow.obj f) ≫
        ((complexCorestrictOpJointIso j).inv.app f).hom.left =
      (complexCorestrict j).op.map ((perfectOppositeJointData X).inl.app f) :=
  oppositeComplexJointDataMapIso_inv_inl _ _ _ _ _ _ _ f

lemma complexCorestrictOpJointIso_inv_inr (f : Arrow (Perfect X)ᵒᵖ) :
    (complexOppositeJointData j).inr.app ((complexCorestrict j).op.mapArrow.obj f) ≫
        ((complexCorestrictOpJointIso j).inv.app f).hom.left =
      (complexCorestrict j).op.map ((perfectOppositeJointData X).inr.app f) :=
  oppositeComplexJointDataMapIso_inv_inr _ _ _ _ _ _ _ f

lemma complexCorestrictOpJointIso_inv_projection (f : Arrow (Perfect X)ᵒᵖ) :
    ((complexCorestrictOpJointIso j).inv.app f).hom.right ≫
        (complexCorestrict j).op.map ((perfectOppositeJointData X).projection.app f) =
      (complexOppositeJointData j).projection.app ((complexCorestrict j).op.mapArrow.obj f) :=
  oppositeComplexJointDataMapIso_inv_projection _ _ _ _ _ _ _ f

end Quillen.PerfectComplexes.OpenDerivedImage
