/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedPullbackFunctor
public import Quillen.Waldhausen.Additivity.GroupFormula
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup

/-!
The unchanged original affine perfect K0 groups and arbitrary geometric pullbacks form a strict
abelian-group-valued ring functor. Flat maps retain the original exact flat-pullback K-map.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.Bass
open Quillen.PerfectComplexes

/-- Only commutativity is added: all original perfect K0 group operations are retained. -/
local instance affineKZeroCommGroup (R : CommRingCat.{u}) : CommGroup (PerfectK (Spec R) 0) :=
  Quillen.Waldhausen.Additivity.KCommGroup (perfectWaldhausen (Spec R)) 0

/-- The literal original affine perfect K0 groups and original geometric pullback maps. -/
def affineKZeroMultiplicativeFunctor : CommRingCat.{u} ⥤ CommGrpCat.{u+1} where
  obj R := .of (PerfectK (Spec R) 0)
  map f := CommGrpCat.ofHom (perfectKPullback (Spec.map f) 0)
  map_id R := by
    apply CommGrpCat.ext
    intro a
    change perfectKPullback (Spec.map (𝟙 R)) 0 a = a
    rw [Spec.map_id,perfectKPullback_id]
    rfl
  map_comp f g := by
    apply CommGrpCat.ext
    intro a
    change perfectKPullback (Spec.map (f ≫ g)) 0 a =
      perfectKPullback (Spec.map g) 0 (perfectKPullback (Spec.map f) 0 a)
    rw [Spec.map_comp,perfectKPullback_comp]
    rfl

/-- The same original K0 group law in additive notation, as a strict ring functor. -/
def affineKZeroFunctor : CommRingCat.{u} ⥤ AddCommGrpCat.{u+1} :=
  affineKZeroMultiplicativeFunctor ⋙ CommGrpCat.toAddCommGrp

@[simp] lemma affineKZeroFunctor_map {R S : CommRingCat.{u}} (f : R ⟶ S)
    (a : PerfectK (Spec R) 0) :
    (affineKZeroFunctor.map f) (Additive.ofMul a) =
      Additive.ofMul (perfectKPullback (Spec.map f) 0 a) := rfl

/-- For flat affine maps, these are literally the old exact flat-pullback K-maps. -/
lemma affineKZeroFunctor_map_flat {R S : CommRingCat.{u}} (f : R ⟶ S)
    [Flat (Spec.map f)] (a : PerfectK (Spec R) 0) :
    (affineKZeroFunctor.map f) (Additive.ofMul a) =
      Additive.ofMul (perfectKFlatPullback (Spec.map f) 0 a) := by
  rw [affineKZeroFunctor_map, perfectKPullback_eq_flatPullback]

end Quillen.Bass

end
