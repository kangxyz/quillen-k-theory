/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.Fibration.Rows.OppositeComplexJointInclusion
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenFibration

/-!
# Coherent actual cocylinders for strict and locally perfect complexes

On every scheme, the literal opposites of the original strict-perfect and
locally-perfect categories carry Waldhausen structures with original admissible
epimorphism cofibrations. Their joint data is obtained from the same actual
ambient opposite-complex cylinder. The original strict-to-perfect inclusion is
exact and intertwines both endpoints and the weak projection coherently.

No affine, quasi-compact, termwise-quasicoherent, or global-bound hypothesis is
needed for these structural constructions. No K-equivalence is asserted here.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes
open Waldhausen Fibration

/-- Original strict complexes with admissible epi cofibrations on their opposite. -/
def strictOppositeWaldhausen (X : Scheme.{u}) : Structure (StrictPerfect X)ᵒᵖ :=
  oppositeComplexSubcategory (strictPerfect X)

/-- Original locally perfect complexes with admissible epi opposite cofibrations. -/
def perfectOppositeWaldhausen (X : Scheme.{u}) : Structure (Perfect X)ᵒᵖ :=
  oppositeComplexSubcategory (locallyPerfect X)

lemma strictOppositeWaldhausen_compatible (X : Scheme.{u}) :
    IsCompatibleDual (strictWaldhausen X) (strictOppositeWaldhausen X) :=
  oppositeComplexSubcategory_compatible (strictPerfect X)

lemma perfectOppositeWaldhausen_compatible (X : Scheme.{u}) :
    IsCompatibleDual (perfectWaldhausen X) (perfectOppositeWaldhausen X) :=
  oppositeComplexSubcategory_compatible (locallyPerfect X)

/-- The literal strict-to-perfect inclusion is exact for both dual structures. -/
lemma strictToPerfect_op_exact (X : Scheme.{u}) : IsExact
    (strictOppositeWaldhausen X).cof (strictOppositeWaldhausen X).weq
    (perfectOppositeWaldhausen X).cof (perfectOppositeWaldhausen X).weq (strictToPerfect X).op :=
  oppositeSubcategoryInclusion_exact (strictPerfect X) (locallyPerfect X)
    (fun _ h => locallyPerfect_of_strictPerfect h)

/-- The actual strict cocylinder is the transported common ambient cylinder. -/
def strictOppositeJointData (X : Scheme.{u}) :
    RowFactorization.JointData (NestedWeakEquivalences.refl (strictOppositeWaldhausen X)) :=
  oppositeComplexJointData (strictPerfect X) (fun _ h => strictPerfect_shift h (-1))

/-- The actual perfect cocylinder uses the same ambient formula on every scheme. -/
def perfectOppositeJointData (X : Scheme.{u}) :
    RowFactorization.JointData (NestedWeakEquivalences.refl (perfectOppositeWaldhausen X)) :=
  oppositeComplexJointData (locallyPerfect X) (fun _ h => locallyPerfect_shift h (-1))

/-- The common ambient cocylinder coherently intertwines the actual inclusion. -/
def strictToPerfectOpJointIso (X : Scheme.{u}) :
    (strictOppositeJointData X).joint ⋙
      ExtensionCategory.postcompose (strictOppositeWaldhausen X) (perfectOppositeWaldhausen X)
        (strictToPerfect_op_exact X) ≅
      (strictToPerfect X).op.mapArrow ⋙ (perfectOppositeJointData X).joint :=
  oppositeComplexJointDataInclusionIso (strictPerfect X) (locallyPerfect X)
    (fun _ h => locallyPerfect_of_strictPerfect h)
    (fun _ h => strictPerfect_shift h (-1)) (fun _ h => locallyPerfect_shift h (-1))

lemma strictToPerfectOpJointIso_inv_inl (X : Scheme.{u}) (f : Arrow (StrictPerfect X)ᵒᵖ) :
    (perfectOppositeJointData X).inl.app ((strictToPerfect X).op.mapArrow.obj f) ≫
      ((strictToPerfectOpJointIso X).inv.app f).hom.left =
    (strictToPerfect X).op.map ((strictOppositeJointData X).inl.app f) :=
  oppositeComplexJointDataInclusionIso_inv_inl _ _ _ _ _ f

lemma strictToPerfectOpJointIso_inv_inr (X : Scheme.{u}) (f : Arrow (StrictPerfect X)ᵒᵖ) :
    (perfectOppositeJointData X).inr.app ((strictToPerfect X).op.mapArrow.obj f) ≫
      ((strictToPerfectOpJointIso X).inv.app f).hom.left =
    (strictToPerfect X).op.map ((strictOppositeJointData X).inr.app f) :=
  oppositeComplexJointDataInclusionIso_inv_inr _ _ _ _ _ f

lemma strictToPerfectOpJointIso_inv_projection (X : Scheme.{u}) (f : Arrow (StrictPerfect X)ᵒᵖ) :
    ((strictToPerfectOpJointIso X).inv.app f).hom.right ≫
      (strictToPerfect X).op.map ((strictOppositeJointData X).projection.app f) =
    (perfectOppositeJointData X).projection.app ((strictToPerfect X).op.mapArrow.obj f) :=
  oppositeComplexJointDataInclusionIso_inv_projection _ _ _ _ _ f

end Quillen.PerfectComplexes
