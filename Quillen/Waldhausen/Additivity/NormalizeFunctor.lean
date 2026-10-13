/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.PointedFunctor

/-! # Chosen-object normalization with independent universe levels

The arrow category can have a larger object universe than the original
category. This is the same actual object replacement/conjugation as the
existing pointed functor, generalized to allow that internal use. At equal
universe levels it agrees with the existing canonical `rebaseFunctor`.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v u' v'

namespace Quillen.Waldhausen.Additivity

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- Replace only the specified object's image. -/
def normalizedObject (F : C ⥤ D) (c : C) (d : D) (X : C) : D := by
  classical
  exact if X = c then d else F.obj X

/-- The actual objectwise identification used for conjugation. -/
def normalizationIsoAt (F : C ⥤ D) (c : C) (d : D) (e : F.obj c ≅ d) (X : C) :
    F.obj X ≅ normalizedObject F c d X := by
  classical
  exact if h : X = c then
    eqToIso (congrArg F.obj h) ≪≫ e ≪≫ eqToIso (by simp [normalizedObject, h])
  else eqToIso (by simp [normalizedObject, h])

/-- The actual normalized functor, obtained by objectwise conjugation. -/
def normalizedFunctor (F : C ⥤ D) (c : C) (d : D) (e : F.obj c ≅ d) : C ⥤ D :=
  F.copyObj (normalizedObject F c d) (normalizationIsoAt F c d e)

/-- Normalization is naturally isomorphic to the original functor. -/
def normalizationIso (F : C ⥤ D) (c : C) (d : D) (e : F.obj c ≅ d) :
    F ≅ normalizedFunctor F c d e :=
  F.isoCopyObj (normalizedObject F c d) (normalizationIsoAt F c d e)

@[simp] theorem normalizedFunctor_obj_base (F : C ⥤ D) (c : C) (d : D) (e : F.obj c ≅ d) :
    (normalizedFunctor F c d e).obj c = d := by
  classical
  simp [normalizedFunctor, normalizedObject]

section SameUniverses
variable {E : Type u} [Category.{v} E]

/-- The internal universe-general construction retains exactly the existing
canonical functor used by public pointed K-maps. -/
theorem normalizedFunctor_eq_rebase (F : C ⥤ E) (c : C) (d : E) (e : F.obj c ≅ d) :
    normalizedFunctor F c d e = Quillen.rebaseFunctor F c d e := rfl

/-- The natural identification likewise retains the existing canonical one. -/
theorem normalizationIso_eq_rebase (F : C ⥤ E) (c : C) (d : E) (e : F.obj c ≅ d) :
    normalizationIso F c d e = Quillen.rebaseFunctorIso F c d e := rfl
end SameUniverses

end Quillen.Waldhausen.Additivity
