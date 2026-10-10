/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Waldhausen.Functor
public import Quillen.Topology.ClassifyingSpace.PointedFunctor

/-!
# Pointed Waldhausen K-maps

An exact functor preserves the zero object up to its unique isomorphism.
Rebasing the functor along that isomorphism gives an actual pointed map of
S-construction realizations and hence a homomorphism at the chosen basepoints.
-/
@[expose] public section


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Quillen.Waldhausen

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {W : Structure C} {W' : Structure D}

instance Structure.cof_respectsIso (W : Structure C) : W.cof.RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition (fun _ _ _ h ↦ W.cof_iso _ h)

instance Structure.weq_respectsIso (W : Structure C) : W.weq.RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition (fun _ _ _ h ↦ W.weq_iso _ h)

/-- Exactness is preserved under natural isomorphism. -/
theorem IsExact.of_iso {F G : C ⥤ D} (hF : IsExact W.cof W.weq W'.cof W'.weq F)
    (e : F ≅ G) : IsExact W.cof W.weq W'.cof W'.weq G where
  zero hZ := (hF.zero hZ).of_iso (e.app _).symm
  cofibration f hf := by
    have hm : G.map f = (e.app _).inv ≫ F.map f ≫ (e.app _).hom := by
      change G.map f = e.inv.app _ ≫ (F.map f ≫ e.hom.app _)
      rw [e.hom.naturality]
      simp
    rw [hm]
    exact W'.cof.comp_mem _ _ (W'.cof_iso _ inferInstance)
      (W'.cof.comp_mem _ _ (hF.cofibration f hf) (W'.cof_iso _ inferInstance))
  weak f hf := by
    have hm : G.map f = (e.app _).inv ≫ F.map f ≫ (e.app _).hom := by
      change G.map f = e.inv.app _ ≫ (F.map f ≫ e.hom.app _)
      rw [e.hom.naturality]
      simp
    rw [hm]
    exact W'.weq.comp_mem _ _ (W'.weq_iso _ inferInstance)
      (W'.weq.comp_mem _ _ (hF.weak f hf) (W'.weq_iso _ inferInstance))
  pushout hi h := (hF.pushout hi h).of_iso (e.app _) (e.app _) (e.app _) (e.app _)
    (e.hom.naturality _) (e.hom.naturality _) (e.hom.naturality _) (e.hom.naturality _)

/-- Exactness of the canonically rebased functor. -/
theorem IsExact.rebase {F : C ⥤ D} (hF : IsExact W.cof W.weq W'.cof W'.weq F) :
    IsExact W.cof W.weq W'.cof W'.weq
      (Quillen.rebaseFunctor F W.zero W'.zero ((hF.zero W.isZero).iso W'.isZero)) :=
  hF.of_iso (Quillen.rebaseFunctorIso F W.zero W'.zero ((hF.zero W.isZero).iso W'.isZero))

/-- The K-homomorphism induced by an exact functor, at the specified zero
objects of the two Waldhausen structures. -/
def KMap {F : C ⥤ D} (hF : IsExact W.cof W.weq W'.cof W'.weq F) (n : ℕ) :
    W.K n →* W'.K n :=
  groupsMapOfZeroEq hF.rebase W.zero W.isZero W'.zero W'.isZero
    (Quillen.rebaseFunctor_obj_base _ _ _ _) n

end Quillen.Waldhausen
