/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.PerfectComplexes.SupportClosure
import Quillen.PerfectComplexes.OppositeJointData

/-!
# Coherent actual cocylinders for supported perfect complexes

The original strict-supported and perfect-supported predicates define genuine
opposite Waldhausen structures. The same ambient cylinder supplies their joint
data and the exact original inclusion, with all endpoint/projection coherence
identities. The support remains actual open-restriction acyclicity throughout.
No affine or quasi-compact hypothesis is needed for these structures.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry HomologicalComplex
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes
open Waldhausen Fibration
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Literal original supported inclusion underlying the already public K-map. -/
def strictSupportedToPerfect : (strictSupported j).FullSubcategory ⥤
    (perfectSupported j).FullSubcategory :=
  ObjectProperty.ιOfLE (fun _ h => ⟨locallyPerfect_of_strictPerfect h.1, h.2⟩)

lemma strictSupportedToPerfect_exact : IsExact
    (strictSupportedWaldhausen j).cof (strictSupportedWaldhausen j).weq
    (perfectSupportedWaldhausen j).cof (perfectSupportedWaldhausen j).weq
    (strictSupportedToPerfect j) :=
  subcategoryInclusion_exact _ _ (fun _ h => ⟨locallyPerfect_of_strictPerfect h.1, h.2⟩)

def strictSupportedOppositeWaldhausen : Structure (strictSupported j).FullSubcategoryᵒᵖ :=
  oppositeComplexSubcategory (strictSupported j)

def perfectSupportedOppositeWaldhausen : Structure (perfectSupported j).FullSubcategoryᵒᵖ :=
  oppositeComplexSubcategory (perfectSupported j)

lemma strictSupportedOppositeWaldhausen_compatible :
    IsCompatibleDual (strictSupportedWaldhausen j) (strictSupportedOppositeWaldhausen j) :=
  oppositeComplexSubcategory_compatible (strictSupported j)

lemma perfectSupportedOppositeWaldhausen_compatible :
    IsCompatibleDual (perfectSupportedWaldhausen j) (perfectSupportedOppositeWaldhausen j) :=
  oppositeComplexSubcategory_compatible (perfectSupported j)

lemma strictSupportedToPerfect_op_exact : IsExact
    (strictSupportedOppositeWaldhausen j).cof (strictSupportedOppositeWaldhausen j).weq
    (perfectSupportedOppositeWaldhausen j).cof (perfectSupportedOppositeWaldhausen j).weq
    (strictSupportedToPerfect j).op :=
  oppositeSubcategoryInclusion_exact _ _ (fun _ h => ⟨locallyPerfect_of_strictPerfect h.1, h.2⟩)

def strictSupportedOppositeJointData : RowFactorization.JointData
    (NestedWeakEquivalences.refl (strictSupportedOppositeWaldhausen j)) :=
  oppositeComplexJointData (strictSupported j) (fun _ h => strictSupported_shift j h (-1))

def perfectSupportedOppositeJointData : RowFactorization.JointData
    (NestedWeakEquivalences.refl (perfectSupportedOppositeWaldhausen j)) :=
  oppositeComplexJointData (perfectSupported j) (fun _ h => perfectSupported_shift j h (-1))

def strictSupportedToPerfect_op_jointIso :
    (strictSupportedOppositeJointData j).joint ⋙
      ExtensionCategory.postcompose (strictSupportedOppositeWaldhausen j)
        (perfectSupportedOppositeWaldhausen j) (strictSupportedToPerfect_op_exact j) ≅
      (strictSupportedToPerfect j).op.mapArrow ⋙ (perfectSupportedOppositeJointData j).joint :=
  oppositeComplexJointData_inclusionIso (strictSupported j) (perfectSupported j)
    (fun _ h => ⟨locallyPerfect_of_strictPerfect h.1, h.2⟩)
    (fun _ h => strictSupported_shift j h (-1)) (fun _ h => perfectSupported_shift j h (-1))

lemma strictSupportedToPerfect_op_jointIso_inv_inl
    (f : Arrow (strictSupported j).FullSubcategoryᵒᵖ) :
    (perfectSupportedOppositeJointData j).inl.app ((strictSupportedToPerfect j).op.mapArrow.obj f) ≫
      ((strictSupportedToPerfect_op_jointIso j).inv.app f).hom.left =
    (strictSupportedToPerfect j).op.map ((strictSupportedOppositeJointData j).inl.app f) :=
  oppositeComplexJointData_inclusionIso_inv_inl _ _ _ _ _ f

lemma strictSupportedToPerfect_op_jointIso_inv_inr
    (f : Arrow (strictSupported j).FullSubcategoryᵒᵖ) :
    (perfectSupportedOppositeJointData j).inr.app ((strictSupportedToPerfect j).op.mapArrow.obj f) ≫
      ((strictSupportedToPerfect_op_jointIso j).inv.app f).hom.left =
    (strictSupportedToPerfect j).op.map ((strictSupportedOppositeJointData j).inr.app f) :=
  oppositeComplexJointData_inclusionIso_inv_inr _ _ _ _ _ f

lemma strictSupportedToPerfect_op_jointIso_inv_projection
    (f : Arrow (strictSupported j).FullSubcategoryᵒᵖ) :
    ((strictSupportedToPerfect_op_jointIso j).inv.app f).hom.right ≫
      (strictSupportedToPerfect j).op.map ((strictSupportedOppositeJointData j).projection.app f) =
    (perfectSupportedOppositeJointData j).projection.app ((strictSupportedToPerfect j).op.mapArrow.obj f) :=
  oppositeComplexJointData_inclusionIso_inv_projection _ _ _ _ _ f

end Quillen.PerfectComplexes
