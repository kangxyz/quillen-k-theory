/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.Fibration.Rows.JointFactorization

/-! # Source row factorizations from a genuine base joint cylinder

The reflexive weak-class pair specializes the existing exact joint-arrow
interchange to the original row structure. Its cofibration is the genuine
all-triples Reedy condition. Its projection retains every original base
component. Target row saturation is separately derived componentwise.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v u' v'
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen.Fibration.NestedWeakEquivalences
variable {C : Type u} [Category.{v} C]

/-- The reflexive pair of weak classes retains the literal entire structure. -/
def refl (W : Structure C) : NestedWeakEquivalences W where
  coarse := W
  cof_eq := rfl
  zero_eq := rfl
  le_weq := le_rfl

end Quillen.Waldhausen.Fibration.NestedWeakEquivalences

namespace Quillen.Waldhausen.QuotientRows
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- Honest base joint-cylinder data constructs a genuine source factorization
on each actual row, including degree zero and all joint cofibration tests. -/
def factorizationOfJointData
    (D : Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl W))
    (n : SimplexCategory) : FunctorialFactorization (waldhausenStructure W n) :=
  Fibration.RowFactorization.factorization (Fibration.NestedWeakEquivalences.refl W) D n

/-- The source row projection is literally the given base projection at every interval. -/
@[simp] theorem factorizationOfJointData_projection_app
    (D : Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl W))
    {n : SimplexCategory} (f : Arrow (Obj W n)) (p : Interval n) :
    ((factorizationOfJointData W D n).projection.app f).hom.app p =
      D.projection.app (Arrow.mk (f.hom.hom.app p)) := rfl

/-- Its first row factor is the genuine componentwise endpoint/joint composite. -/
@[simp] theorem factorizationOfJointData_inclusion_app
    (D : Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl W))
    {n : SimplexCategory} (f : Arrow (Obj W n)) (p : Interval n) :
    ((factorizationOfJointData W D n).inclusion.app f).hom.app p =
      D.inl.app (Arrow.mk (f.hom.hom.app p)) ≫
        (D.joint.obj (Arrow.mk (f.hom.hom.app p))).obj.hom := rfl

instance waldhausenStructure_twoOutOfThree (n : SimplexCategory)
    [W.weq.HasTwoOutOfThreeProperty] : (waldhausenStructure W n).weq.HasTwoOutOfThreeProperty :=
  { comp_mem := fun _ _ hf hg p ↦ W.weq.comp_mem _ _ (hf p) (hg p)
    of_postcomp := fun f g hg hfg p ↦ W.weq.of_postcomp (f.hom.app p) (g.hom.app p) (hg p) (hfg p)
    of_precomp := fun f g hf hfg p ↦ W.weq.of_precomp (f.hom.app p) (g.hom.app p) (hf p) (hfg p) }

end Quillen.Waldhausen.QuotientRows
