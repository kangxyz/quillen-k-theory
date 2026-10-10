/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.Fibration.Rows.OppositeComplexJointMap
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.Structure

/-!
# Original restriction cocylinders in the derived-saturated image

The actual exact open restriction, with its literal derived-image witness,
intertwines the original common opposite cocylinders. The natural isomorphism
retains the exact first endpoint, second endpoint and projection equations.
The target image structures use the explicit genuine derived-roof property;
no approximation or localization conclusion is assumed here.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Quillen.PerfectComplexes.OpenDerivedImage
open Waldhausen Fibration
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [Fact (HasDerivedRoofs j)]

/-- The literal original corestriction preserves the actual common opposite cocylinder. -/
def complexCorestrict_op_jointIso :
    (perfectOppositeJointData X).joint ⋙
      ExtensionCategory.postcompose (perfectOppositeWaldhausen X) (complexOppositeWaldhausen j)
        (complexCorestrict_op_exact j) ≅
      (complexCorestrict j).op.mapArrow ⋙ (complexOppositeJointData j).joint :=
  oppositeComplexJointData_mapIso (Scheme.Modules.restrictFunctor j)
    (locallyPerfect X) (complexObjects j) (fun K hK => ⟨K, hK, ⟨Iso.refl _⟩⟩)
    (fun _ h => locallyPerfect_shift h (-1)) (fun _ h => complexObjects_shift j h (-1))
    (complexCorestrict_op_exact j)

lemma complexCorestrict_op_jointIso_inv_inl (f : Arrow (Perfect X)ᵒᵖ) :
    (complexOppositeJointData j).inl.app ((complexCorestrict j).op.mapArrow.obj f) ≫
        ((complexCorestrict_op_jointIso j).inv.app f).hom.left =
      (complexCorestrict j).op.map ((perfectOppositeJointData X).inl.app f) :=
  oppositeComplexJointData_mapIso_inv_inl _ _ _ _ _ _ _ f

lemma complexCorestrict_op_jointIso_inv_inr (f : Arrow (Perfect X)ᵒᵖ) :
    (complexOppositeJointData j).inr.app ((complexCorestrict j).op.mapArrow.obj f) ≫
        ((complexCorestrict_op_jointIso j).inv.app f).hom.left =
      (complexCorestrict j).op.map ((perfectOppositeJointData X).inr.app f) :=
  oppositeComplexJointData_mapIso_inv_inr _ _ _ _ _ _ _ f

lemma complexCorestrict_op_jointIso_inv_projection (f : Arrow (Perfect X)ᵒᵖ) :
    ((complexCorestrict_op_jointIso j).inv.app f).hom.right ≫
        (complexCorestrict j).op.map ((perfectOppositeJointData X).projection.app f) =
      (complexOppositeJointData j).projection.app ((complexCorestrict j).op.mapArrow.obj f) :=
  oppositeComplexJointData_mapIso_inv_projection _ _ _ _ _ _ _ f

end Quillen.PerfectComplexes.OpenDerivedImage
