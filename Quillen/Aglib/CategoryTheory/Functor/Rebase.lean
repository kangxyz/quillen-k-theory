/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.CategoryTheory.EqToHom


/-!
# Ordinary functors rebased at one chosen object

A specified isomorphism `F.obj c ≅ d` changes only the chosen object image and
conjugates the actual arrow maps. The original comparison is a natural
isomorphism; the chosen image is literally `d`, and reflexive rebasing is the
original functor. No realization or homotopy-group construction occurs here.
-/
@[expose] public section




noncomputable section

open CategoryTheory

universe v u

namespace Quillen

variable {C : Type u} {D : Type u} [Category.{v} C] [Category.{v} D]

/-- Replace the image of one specified object by the desired target object. -/
def rebaseObj (F : C ⥤ D) (c : C) (d : D) (X : C) : D :=
  by
    classical
    exact if X = c then d else F.obj X

/-- The pointwise comparison with the original object map. -/
def rebaseObjIso (F : C ⥤ D) (c : C) (d : D) (e : F.obj c ≅ d) (X : C) :
    F.obj X ≅ rebaseObj F c d X := by
  classical
  exact if h : X = c then
    eqToIso (congrArg F.obj h) ≪≫ e ≪≫ eqToIso (by simp [rebaseObj, h])
  else
    eqToIso (by simp [rebaseObj, h])

/-- Conjugate the original arrow map by the chosen objectwise isomorphisms. -/
def rebaseFunctor (F : C ⥤ D) (c : C) (d : D) (e : F.obj c ≅ d) : C ⥤ D where
  obj := rebaseObj F c d
  map {X Y} f := (rebaseObjIso F c d e X).inv ≫ F.map f ≫
    (rebaseObjIso F c d e Y).hom
  map_id X := by simp
  map_comp f g := by simp [Category.assoc]

/-- Rebasing gives a naturally isomorphic functor. -/
def rebaseFunctorIso (F : C ⥤ D) (c : C) (d : D) (e : F.obj c ≅ d) :
    F ≅ rebaseFunctor F c d e :=
  NatIso.ofComponents (rebaseObjIso F c d e) (by
    intros X Y f
    simp [rebaseFunctor])

/-- The rebased functor takes the source base object to the target base object. -/
@[simp]
theorem rebaseFunctor_obj_base (F : C ⥤ D) (c : C) (d : D) (e : F.obj c ≅ d) :
    (rebaseFunctor F c d e).obj c = d := by
  classical
  simp [rebaseFunctor, rebaseObj]

/-- Rebasing along the reflexive isomorphism leaves the functor unchanged. -/
@[simp]
theorem rebaseFunctor_refl (F : C ⥤ D) (c : C) :
    rebaseFunctor F c (F.obj c) (Iso.refl _) = F := by
  classical
  have hobj (X : C) : (rebaseFunctor F c (F.obj c) (Iso.refl _)).obj X = F.obj X := by
    by_cases h : X = c
    · subst X
      simp [rebaseFunctor, rebaseObj]
    · simp [rebaseFunctor, rebaseObj, h]
  refine Functor.ext_of_iso (rebaseFunctorIso F c (F.obj c) (Iso.refl _)).symm hobj ?_
  intro X
  dsimp only [rebaseFunctorIso, NatIso.ofComponents, Iso.symm, rebaseObjIso]
  split_ifs with h
  · subst X
    simp
    rfl
  · rfl


end Quillen
