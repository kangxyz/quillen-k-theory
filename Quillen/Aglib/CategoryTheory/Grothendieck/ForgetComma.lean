/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.CategoryTheory.Grothendieck.FiberTransitions
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-! # Original fibers and comma categories of the Grothendieck projection -/

@[expose] public section
noncomputable section
open CategoryTheory
universe u v w t
namespace Quillen.GrothendieckForget
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [Category.{v} C] (F : C ⥤ Cat.{w, t})

/-- The actual fiber entry into the comma category of the original projection. -/
def commaEntry (c : C) : F.obj c ⥤ CostructuredArrow (Grothendieck.forget F) c where
  obj X := CostructuredArrow.mk (Y := (Grothendieck.ι F c).obj X) (𝟙 c)
  map f := CostructuredArrow.homMk ((Grothendieck.ι F c).map f) (by simp)
  map_id X := by
    apply CostructuredArrow.hom_ext
    exact (Grothendieck.ι F c).map_id X
  map_comp f g := by
    apply CostructuredArrow.hom_ext
    exact (Grothendieck.ι F c).map_comp f g

/-- Transport along the original comma structure arrow. -/
abbrev commaTransportObj {c : C} (U : CostructuredArrow (Grothendieck.forget F) c) : F.obj c :=
  (F.map U.hom).toFunctor.obj U.left.fiber

/-- The original cocartesian normal form gives a comma arrow. -/
def commaHom {c : C} (U : CostructuredArrow (Grothendieck.forget F) c) (Y : F.obj c)
    (g : commaTransportObj F U ⟶ Y) : U ⟶ (commaEntry F c).obj Y :=
  CostructuredArrow.homMk ⟨U.hom, g⟩ (by simp [commaEntry])

/-- This normal form is bijective on actual morphisms. -/
theorem commaHom_bijective {c : C} (U : CostructuredArrow (Grothendieck.forget F) c)
    (Y : F.obj c) : Function.Bijective (commaHom F U Y) := by
  constructor
  · intro f g h
    have hh := congrArg (fun k ↦ k.left) h
    simpa [commaHom, commaEntry] using Grothendieck.congr hh
  · intro f
    have hb : f.left.base = U.hom := by
      simpa [commaEntry] using CostructuredArrow.w f
    refine ⟨eqToHom (by rw [hb]) ≫ f.left.fiber, ?_⟩
    apply CostructuredArrow.hom_ext
    refine Grothendieck.ext _ _ hb.symm ?_
    simp [commaHom]

/-- Actual fiber maps represent exactly the comma maps into the original entry. -/
def commaHomEquiv {c : C} (U : CostructuredArrow (Grothendieck.forget F) c) (Y : F.obj c) :
    (commaTransportObj F U ⟶ Y) ≃ (U ⟶ (commaEntry F c).obj Y) :=
  Equiv.ofBijective (commaHom F U Y) (commaHom_bijective F U Y)

/-- The normal form respects postcomposition by the actual fiber inclusion. -/
theorem commaHom_naturality {c : C} (U : CostructuredArrow (Grothendieck.forget F) c)
    {Y Z : F.obj c} (g : commaTransportObj F U ⟶ Y) (k : Y ⟶ Z) :
    commaHom F U Z (g ≫ k) = commaHom F U Y g ≫ (commaEntry F c).map k := by
  apply CostructuredArrow.hom_ext
  calc
    _ = (Grothendieck.ιNatTrans (F := F) U.hom).app U.left.fiber ≫
        (Grothendieck.ι F c).map (g ≫ k) :=
      (Grothendieck.fiberTransition_factorization F (commaHom F U Z (g ≫ k)).left).symm
    _ = ((Grothendieck.ιNatTrans (F := F) U.hom).app U.left.fiber ≫
        (Grothendieck.ι F c).map g) ≫ (Grothendieck.ι F c).map k := by
      rw [Functor.map_comp, Category.assoc]
    _ = _ := congrArg (fun h ↦ h ≫ (Grothendieck.ι F c).map k)
      (Grothendieck.fiberTransition_factorization F (commaHom F U Y g).left)


/-- Transport is the actual left adjoint to the original comma entry. -/
def commaTransport (c : C) : CostructuredArrow (Grothendieck.forget F) c ⥤ F.obj c :=
  Adjunction.leftAdjointOfEquiv (fun U Y ↦ commaHomEquiv F U Y)
    (fun U _ _ g h ↦ commaHom_naturality F U h g)

/-- The actual adjunction identifies original comma spaces with original fibers. -/
def commaTransportAdjunction (c : C) : commaTransport F c ⊣ commaEntry F c :=
  Adjunction.adjunctionOfEquivLeft _ _

/-- The original fiber inclusion factors through the original comma projection. -/
theorem commaEntry_projection (c : C) :
    commaEntry F c ⋙ CostructuredArrow.proj (Grothendieck.forget F) c =
      Grothendieck.ι F c := rfl

/-- The original diagram transition compares the two actual comma entries. -/
def commaEntryTransition {c d : C} (f : c ⟶ d) :
    commaEntry F c ⋙ CostructuredArrow.map (S := Grothendieck.forget F) f ⟶
      (F.map f).toFunctor ⋙ commaEntry F d where
  app X := CostructuredArrow.homMk ((Grothendieck.ιNatTrans (F := F) f).app X)
    (by simp [commaEntry, Grothendieck.ιNatTrans])
  naturality {X Y} g := by
    apply CostructuredArrow.hom_ext
    exact (Grothendieck.ιNatTrans (F := F) f).naturality g

end Quillen.GrothendieckForget
