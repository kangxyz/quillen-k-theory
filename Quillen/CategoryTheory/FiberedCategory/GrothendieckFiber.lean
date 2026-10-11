/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.Grothendieck
public import Mathlib.CategoryTheory.FiberedCategory.Fiber

/-!
# The original category and its covariant Grothendieck fiber

The forward functor retains the original pseudofunctor identity comparison. A concrete inverse
retains the original fiber object with only its proved base equality transported; it does not
choose a replacement object. Both categorical equivalence and this concrete inverse are provided.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Bicategory
open scoped CategoryTheory.Pseudofunctor.Grothendieck
universe u v u' v'
namespace Quillen.CategoryTheory.GrothendieckFiber
variable {C : Type u} [Category.{v} C]
  (F : Pseudofunctor (LocallyDiscrete C) Cat.{v', u'}) (R : C)

set_option backward.isDefEq.respectTransparency false in
attribute [local simp] PrelaxFunctor.map₂_eqToHom in
/-- The original category includes into its Grothendieck total category over the identity. -/
def inclusion : F.obj ⟨R⟩ ⥤ Pseudofunctor.Grothendieck F where
  obj x := ⟨R, x⟩
  map {x y} f := ⟨𝟙 R, (F.mapId ⟨R⟩).hom.toNatTrans.app x ≫ f⟩
  map_id x := by
    refine Pseudofunctor.Grothendieck.Hom.ext _ _ rfl ?_
    simp
  map_comp {x y z} f g := by
    refine Pseudofunctor.Grothendieck.Hom.ext _ _ (by simp) ?_
    simp [F.mapComp_id_right_hom_app, Strict.rightUnitor_eqToIso]

/-- The inclusion is literally over the constant base object. -/
theorem inclusion_comp : inclusion F R ⋙ Pseudofunctor.Grothendieck.forget F =
    (Functor.const (F.obj ⟨R⟩)).obj R := rfl

/-- The original category maps to the actual fiber, retaining the original identity comparison. -/
def toFiber : F.obj ⟨R⟩ ⥤ Functor.Fiber (Pseudofunctor.Grothendieck.forget F) R :=
  Functor.Fiber.inducedFunctor (inclusion_comp F R)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
instance : (toFiber F R).Full where
  map_surjective {x y} f := by
    have := f.property
    have hf : f.val.base = 𝟙 R := by
      simpa using (IsHomLift.fac (Pseudofunctor.Grothendieck.forget F) (𝟙 R) f.val).symm
    refine ⟨(F.mapId ⟨R⟩).inv.toNatTrans.app x ≫
      eqToHom (by simp [hf, toFiber, Functor.Fiber.inducedFunctor, inclusion]) ≫ f.val.fiber, ?_⟩
    apply Subtype.ext
    refine Pseudofunctor.Grothendieck.Hom.ext _ _ hf.symm ?_
    simp [toFiber, inclusion, Functor.Fiber.inducedFunctor]

set_option backward.isDefEq.respectTransparency false in
instance : (toFiber F R).Faithful where
  map_injective {x y} f g h := by
    have hh := congrArg Subtype.val h
    have hh' := (Pseudofunctor.Grothendieck.Hom.ext_iff _ _).mp hh
    obtain ⟨e, he⟩ := hh'
    simpa [toFiber, inclusion, Functor.Fiber.inducedFunctor, ← Cat.Hom.toNatIso_hom] using he

set_option backward.defeqAttrib.useBackward true in
instance : (toFiber F R).EssSurj := by
  apply Functor.essSurj_of_surj
  rintro ⟨⟨S, y⟩, hy⟩
  change S = R at hy
  subst S
  exact ⟨y, rfl⟩

instance : (toFiber F R).IsEquivalence where

/-- Evaluation of a Grothendieck fiber is equivalent to the original pseudofunctor category. -/
def equivalence : F.obj ⟨R⟩ ≌ Functor.Fiber (Pseudofunctor.Grothendieck.forget F) R :=
  (toFiber F R).asEquivalence

/-- The original fiber object, transported only along its proved base equality. -/
def originalObject (x : Functor.Fiber (Pseudofunctor.Grothendieck.forget F) R) : F.obj ⟨R⟩ :=
  x.property ▸ x.val.fiber

/-- Re-including the original fiber object recovers the actual fiber object literally. -/
theorem toFiber_originalObject (x : Functor.Fiber (Pseudofunctor.Grothendieck.forget F) R) :
    (toFiber F R).obj (originalObject F R x) = x := by
  rcases x with ⟨⟨S, x⟩, hx⟩
  change S = R at hx
  subst S
  rfl

/-- A concrete inverse whose object is the original transported fiber. -/
def fromFiber : Functor.Fiber (Pseudofunctor.Grothendieck.forget F) R ⥤ F.obj ⟨R⟩ where
  obj := originalObject F R
  map {x y} f := (toFiber F R).preimage
    (eqToHom (toFiber_originalObject F R x) ≫ f ≫ eqToHom (toFiber_originalObject F R y).symm)
  map_id x := by
    apply (toFiber F R).map_injective
    simp
  map_comp f g := by
    apply (toFiber F R).map_injective
    simp

/-- The concrete inverse retains each actual fiber object after re-inclusion. -/
def fromFiberCompIso : fromFiber F R ⋙ toFiber F R ≅ 𝟭 _ :=
  NatIso.ofComponents (fun x => eqToIso (toFiber_originalObject F R x)) (by
    intro x y f
    simp [fromFiber])

instance instIsEquivalenceFromFiber : (fromFiber F R).IsEquivalence := by
  have : (fromFiber F R ⋙ toFiber F R).IsEquivalence :=
    Functor.isEquivalence_of_iso (fromFiberCompIso F R).symm
  exact Functor.isEquivalence_of_comp_right (fromFiber F R) (toFiber F R)

end Quillen.CategoryTheory.GrothendieckFiber
