/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.CartesianBaseChange
public import Quillen.CategoryTheory.Adjunction.MateHomEquiv

/-! # Horizontal pasting of the original geometric base-change mate -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Quillen.SchemeSheaf
open Scheme.Modules
/-- The original geometric composite adjunction unit retains the pullback comparison. -/
theorem pullbackAdjunctionUnit_comp {Y Z T : Scheme.{u}} (c : T ⟶ Y) (a : Y ⟶ Z)
    (M : Z.Modules) :
    (pullbackPushforwardAdjunction a).unit.app M ≫
      (pushforward a).map ((pullbackPushforwardAdjunction c).unit.app
        ((Scheme.Modules.pullback a).obj M)) ≫
      (pushforward a).map ((pushforward c).map ((pullbackComp c a).hom.app M)) ≫
      (pushforwardComp c a).hom.app ((Scheme.Modules.pullback (c ≫ a)).obj M) =
      (pullbackPushforwardAdjunction (c ≫ a)).unit.app M := by
  have hc := unit_conjugateEquiv
    ((pullbackPushforwardAdjunction a).comp (pullbackPushforwardAdjunction c))
    (pullbackPushforwardAdjunction (c ≫ a)) (pullbackComp c a).inv M
  rw [conjugateEquiv_pullbackComp_inv] at hc
  have he := congrArg (fun t => t ≫
    (pushforward (c ≫ a)).map ((pullbackComp c a).hom.app M)) hc
  have hn := (pushforwardComp c a).hom.naturality ((pullbackComp c a).hom.app M)
  dsimp only [Functor.comp_map] at hn
  rw [Category.assoc, ← hn] at he
  simpa only [Adjunction.comp_unit_app, Functor.id_obj, Functor.comp_obj,
    Category.assoc, ← Functor.map_comp,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.comp_id] using he
variable {W' W U V' V X : Scheme.{u}}
  (c : W' ⟶ W) (d : W' ⟶ V') (k : V' ⟶ V)
  (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  (hs : IsPullback c d b k) (h : IsPullback a b f j)
/-- Original pushforward square comparison respects horizontal geometric pasting. -/
theorem cartesianPushforwardSquare_paste_horiz (N : W'.Modules) :
    (pushforward f).map ((pushforwardComp c a).hom.app N) ≫
        (cartesianPushforwardSquare (c ≫ a) d f (k ≫ j) (hs.paste_horiz h)).hom.app N =
      (cartesianPushforwardSquare a b f j h).hom.app ((pushforward c).obj N) ≫
        (pushforward j).map ((cartesianPushforwardSquare c d b k hs).hom.app N) ≫
        (pushforwardComp k j).hom.app ((pushforward d).obj N) := by
  ext O x
  simp only [cartesianPushforwardSquare, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Scheme.Modules.Hom.comp_app,
    pushforwardComp_hom_app_app, pushforwardComp_inv_app_app,
    pushforward_map_app, pushforwardCongr_hom_app_app,
    Category.comp_id]
  change (N.presheaf.map _) x = (N.presheaf.map _) ((N.presheaf.map _) x)
  rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp]
  congr 2

/-- Transposition of the actual base-change mate is its original unit-square arrow. -/
theorem cartesianBaseChangeMap_homEquiv {D E F G : Scheme.{u}}
    (a : D ⟶ E) (b : D ⟶ F) (f : E ⟶ G) (j : F ⟶ G) (h : IsPullback a b f j)
    (M : E.Modules) :
    (pullbackPushforwardAdjunction j).homEquiv _ _ ((cartesianBaseChangeMap a b f j h).app M) =
      (pushforward f).map ((pullbackPushforwardAdjunction a).unit.app M) ≫
        (cartesianPushforwardSquare a b f j h).hom.app ((Scheme.Modules.pullback a).obj M) := by
  simpa only [Adjunction.homEquiv_unit] using (cartesianBaseChangeMap_unit a b f j h M).symm
private theorem cartesianBaseChangeMap_paste_horiz_aux (M : U.Modules) :
    (pushforward f).map ((pullbackPushforwardAdjunction (c ≫ a)).unit.app M) ≫
      (cartesianPushforwardSquare (c ≫ a) d f (k ≫ j) (hs.paste_horiz h)).hom.app
        ((Scheme.Modules.pullback (c ≫ a)).obj M) =
    (((pushforward f).map ((pullbackPushforwardAdjunction a).unit.app M) ≫
      (cartesianPushforwardSquare a b f j h).hom.app ((Scheme.Modules.pullback a).obj M)) ≫
      (pushforward j).map
        (((pushforward b).map ((pullbackPushforwardAdjunction c).unit.app
            ((Scheme.Modules.pullback a).obj M)) ≫
          (cartesianPushforwardSquare c d b k hs).hom.app
            ((Scheme.Modules.pullback c).obj ((Scheme.Modules.pullback a).obj M))) ≫
          (pushforward k).map ((pushforward d).map ((pullbackComp c a).hom.app M)))) ≫
      (pushforwardComp k j).hom.app ((Scheme.Modules.pullback (c ≫ a) ⋙ pushforward d).obj M)
      := by
  simp only [Functor.map_comp, Category.assoc]
  let N := (Scheme.Modules.pullback c).obj ((Scheme.Modules.pullback a).obj M)
  let N' := (Scheme.Modules.pullback (c ≫ a)).obj M
  let q : N ⟶ N' := (pullbackComp c a).hom.app M
  have hkj := (pushforwardComp k j).hom.naturality ((pushforward d).map q)
  dsimp only [Functor.comp_map] at hkj
  erw [hkj]
  have ha := (cartesianPushforwardSquare a b f j h).hom.naturality
    ((pullbackPushforwardAdjunction c).unit.app ((Scheme.Modules.pullback a).obj M))
  dsimp only [Functor.comp_map] at ha
  erw [← reassoc_of% ha]
  erw [← reassoc_of% cartesianPushforwardSquare_paste_horiz c d k a b f j hs h N]
  have hb := (cartesianPushforwardSquare (c ≫ a) d f (k ≫ j)
    (hs.paste_horiz h)).hom.naturality q
  dsimp only [Functor.comp_map] at hb
  erw [← hb]
  have hca := congrArg (fun t => (pushforward f).map t)
    ((pushforwardComp c a).hom.naturality q)
  dsimp only [Functor.comp_map] at hca
  simp only [Functor.map_comp] at hca
  have hu := congrArg (fun t => (pushforward f).map t ≫
    (cartesianPushforwardSquare (c ≫ a) d f (k ≫ j)
      (hs.paste_horiz h)).hom.app N') (pullbackAdjunctionUnit_comp c a M)
  have ht := congrArg (fun t =>
    (pushforward f).map ((pullbackPushforwardAdjunction a).unit.app M) ≫
    (pushforward f).map ((pushforward a).map
      ((pullbackPushforwardAdjunction c).unit.app ((Scheme.Modules.pullback a).obj M))) ≫
    t ≫ (cartesianPushforwardSquare (c ≫ a) d f (k ≫ j)
      (hs.paste_horiz h)).hom.app N') hca
  simp only [Functor.map_comp, Category.assoc, Functor.comp_obj] at hu ht
  exact hu.symm.trans ht

/-- The actual base-change mate retains the original horizontal pullback-composition maps. -/
theorem cartesianBaseChangeMap_paste_horiz (M : U.Modules) :
    (pullbackComp k j).hom.app ((pushforward f).obj M) ≫
        (cartesianBaseChangeMap (c ≫ a) d f (k ≫ j) (hs.paste_horiz h)).app M =
      (Scheme.Modules.pullback k).map ((cartesianBaseChangeMap a b f j h).app M) ≫
        (cartesianBaseChangeMap c d b k hs).app ((Scheme.Modules.pullback a).obj M) ≫
        (pushforward d).map ((pullbackComp c a).hom.app M) := by
  have he : (cartesianBaseChangeMap (c ≫ a) d f (k ≫ j) (hs.paste_horiz h)).app M =
      (pullbackComp k j).inv.app ((pushforward f).obj M) ≫
      (Scheme.Modules.pullback k).map ((cartesianBaseChangeMap a b f j h).app M) ≫
        (cartesianBaseChangeMap c d b k hs).app ((Scheme.Modules.pullback a).obj M) ≫
        (pushforward d).map ((pullbackComp c a).hom.app M) := by
    apply ((pullbackPushforwardAdjunction (k ≫ j)).homEquiv _ _).injective
    rw [homEquiv_conjugate, conjugateEquiv_pullbackComp_inv, Adjunction.comp_homEquiv]
    change _ = (pullbackPushforwardAdjunction j).homEquiv _ _
      ((pullbackPushforwardAdjunction k).homEquiv _ _
        ((Scheme.Modules.pullback k).map ((cartesianBaseChangeMap a b f j h).app M) ≫
          (cartesianBaseChangeMap c d b k hs).app ((Scheme.Modules.pullback a).obj M) ≫
          (pushforward d).map ((pullbackComp c a).hom.app M))) ≫ _
    erw [(pullbackPushforwardAdjunction k).homEquiv_naturality_left
      ((cartesianBaseChangeMap a b f j h).app M)
      ((cartesianBaseChangeMap c d b k hs).app ((Scheme.Modules.pullback a).obj M) ≫
        (pushforward d).map ((pullbackComp c a).hom.app M))]
    erw [(pullbackPushforwardAdjunction k).homEquiv_naturality_right
      ((cartesianBaseChangeMap c d b k hs).app ((Scheme.Modules.pullback a).obj M))
      ((pushforward d).map ((pullbackComp c a).hom.app M))]
    erw [cartesianBaseChangeMap_homEquiv (c ≫ a) d f (k ≫ j) (hs.paste_horiz h) M,
      cartesianBaseChangeMap_homEquiv c d b k hs ((Scheme.Modules.pullback a).obj M)]
    simp only [Adjunction.homEquiv_naturality_right]
    erw [cartesianBaseChangeMap_homEquiv a b f j h M]
    exact cartesianBaseChangeMap_paste_horiz_aux c d k a b f j hs h M
  rw [he, Iso.hom_inv_id_app_assoc]
end Quillen.SchemeSheaf
