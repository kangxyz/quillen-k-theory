/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.CartesianBaseChange

/-! # Pasting of the original cartesian base-change mates -/

@[expose] public section
open Quillen
open Quillen.SchemeSheaf

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
open Scheme.Modules
variable {Z' Z W U V X : Scheme.{u}}
  (c : Z' ⟶ Z) (d : Z' ⟶ W) (g : Z ⟶ U)
  (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  (hs : IsPullback c d g a) (h : IsPullback a b f j)
/-- The original pushforward-square comparisons agree with actual vertical pasting. -/
theorem cartesianPushforwardSquare_paste (N : Z'.Modules) :
    (pushforwardComp g f).hom.app ((pushforward c).obj N) ≫
        (cartesianPushforwardSquare c (d ≫ b) (g ≫ f) j (hs.paste_vert h)).hom.app N ≫
        (pushforward j).map ((pushforwardComp d b).inv.app N) =
      (pushforward f).map ((cartesianPushforwardSquare c d g a hs).hom.app N) ≫
        (cartesianPushforwardSquare a b f j h).hom.app ((pushforward d).obj N) := by
  ext O x
  simp only [cartesianPushforwardSquare, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Scheme.Modules.Hom.comp_app,
    pushforwardComp_hom_app_app, pushforwardComp_inv_app_app,
    pushforward_map_app, pushforwardCongr_hom_app_app,
    Category.id_comp, Category.comp_id]
  change (N.presheaf.map _) x = (N.presheaf.map _) ((N.presheaf.map _) x)
  rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp]
  congr 2

/-- The literal geometric mates agree with vertical cartesian pasting. -/
theorem cartesianBaseChangeMap_paste (M : Z.Modules) :
    (Scheme.Modules.pullback j).map ((pushforwardComp g f).hom.app M) ≫
        (cartesianBaseChangeMap c (d ≫ b) (g ≫ f) j (hs.paste_vert h)).app M ≫
        (pushforwardComp d b).inv.app ((Scheme.Modules.pullback c).obj M) =
      (cartesianBaseChangeMap a b f j h).app ((pushforward g).obj M) ≫
        (pushforward b).map ((cartesianBaseChangeMap c d g a hs).app M) := by
  apply ((pullbackPushforwardAdjunction j).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have hn := (pullbackPushforwardAdjunction j).unit.naturality
    ((pushforwardComp g f).hom.app M)
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  erw [← reassoc_of% hn]
  erw [← reassoc_of% cartesianBaseChangeMap_unit c (d ≫ b) (g ≫ f) j
    (hs.paste_vert h) M]
  erw [← reassoc_of% cartesianBaseChangeMap_unit a b f j h ((pushforward g).obj M)]
  have hnat := (cartesianPushforwardSquare a b f j h).hom.naturality
    ((cartesianBaseChangeMap c d g a hs).app M)
  dsimp only [Functor.comp_map] at hnat
  erw [← hnat]
  erw [← (pushforward f).map_comp_assoc
    ((pullbackPushforwardAdjunction a).unit.app ((pushforward g).obj M))
    ((pushforward a).map ((cartesianBaseChangeMap c d g a hs).app M))]
  erw [← cartesianBaseChangeMap_unit c d g a hs M]
  rw [(pushforward f).map_comp]
  have hgf := (pushforwardComp g f).hom.naturality
    ((pullbackPushforwardAdjunction c).unit.app M)
  dsimp only [Functor.comp_map] at hgf
  erw [← reassoc_of% hgf]
  erw [cartesianPushforwardSquare_paste c d g a b f j hs h ((Scheme.Modules.pullback c).obj M)]
  simp only [Category.assoc]
  rfl
end AlgebraicGeometry.Scheme.Modules
