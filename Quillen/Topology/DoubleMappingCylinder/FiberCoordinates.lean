/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Topology.DoubleMappingCylinder.LocalComparison

/-! # Exact fibers of a map of double cylinders

Endpoint fibers use the actual closed endpoint embedding. Interior fibers
use the proved open product chart. No fiber/pushout interchange is assumed.
-/
@[expose] public section

open Topology

noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.DoubleCylinder
section Single
variable {A B C D : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
  {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
  (sq : IsPushout (Quillen.intervalEndpoints A) (endMap f g) l e)

include sq in
theorem leftEnd_isEmbedding : IsEmbedding (fun x : B ↦ e (Sum.inl x)) :=
  (isClosedEmbedding_pushout_right sq (isClosedEmbedding_intervalEndpoints A)).isEmbedding.comp
    IsEmbedding.inl

include sq in
theorem rightEnd_isEmbedding : IsEmbedding (fun x : C ↦ e (Sum.inr x)) :=
  (isClosedEmbedding_pushout_right sq (isClosedEmbedding_intervalEndpoints A)).isEmbedding.comp
    IsEmbedding.inr

theorem height_eq_zero_range (x : D) (hx : height f g sq x = 0) :
    ∃ b : B,e (Sum.inl b) = x := by
  rcases Types.eq_or_eq_of_isPushout (sq.map (forget TopCat)) x with
    ⟨⟨a,t⟩,ht⟩ | ⟨b | c,he⟩
  · change l (a,t) = x at ht
    have ht₀ : t.down = 0 := by rw [← ht,height_cylinder] at hx; exact hx
    have ht' : t = ULift.up (0 : unitInterval) := ULift.ext _ _ ht₀
    subst t
    exact ⟨f a,(ConcreteCategory.congr_hom sq.w (Sum.inl a)).symm.trans ht⟩
  · exact ⟨b,he⟩
  · change e (Sum.inr c) = x at he
    have h10 : (1 : unitInterval) = 0 := by
      have hh := (height_right f g sq c).symm.trans ((congrArg (height f g sq) he).trans hx)
      exact hh
    exact False.elim (one_ne_zero h10)

theorem height_eq_one_range (x : D) (hx : height f g sq x = 1) :
    ∃ c : C,e (Sum.inr c) = x := by
  rcases Types.eq_or_eq_of_isPushout (sq.map (forget TopCat)) x with
    ⟨⟨a,t⟩,ht⟩ | ⟨b | c,he⟩
  · change l (a,t) = x at ht
    have ht₁ : t.down = 1 := by rw [← ht,height_cylinder] at hx; exact hx
    have ht' : t = ULift.up (1 : unitInterval) := ULift.ext _ _ ht₁
    subst t
    exact ⟨g a,(ConcreteCategory.congr_hom sq.w (Sum.inr a)).symm.trans ht⟩
  · change e (Sum.inl b) = x at he
    have h01 : (0 : unitInterval) = 1 := by
      exact (height_left f g sq b).symm.trans ((congrArg (height f g sq) he).trans hx)
    exact False.elim (zero_ne_one h01)
  · exact ⟨c,he⟩
end Single

variable {A B C D A' B' C' D' : TopCat.{u}}
  {f : A ⟶ B} {g : A ⟶ C} {f' : A' ⟶ B'} {g' : A' ⟶ C'}
  {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
  {l' : A' ⊗ TopCat.I ⟶ D'} {e' : TopCat.of (B' ⊕ C') ⟶ D'}
  (sq : IsPushout (Quillen.intervalEndpoints A) (endMap f g) l e)
  (sq' : IsPushout (Quillen.intervalEndpoints A') (endMap f' g') l' e')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
  (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g')

/-- The left endpoint fiber is the original endpoint map's strict fiber. -/
def leftEndFiberHomeomorph (y : B') :
    {x : B // b x = y} ≃ₜ {x : D // map sq sq' a b c wf wg x = e' (Sum.inl y)} := by
  let k : C({x : B // b x = y},{x : D // map sq sq' a b c wf wg x = e' (Sum.inl y)}) := {
    toFun x := ⟨e (Sum.inl x.val),(map_left sq sq' a b c wf wg x.val).trans
      (congrArg (fun z ↦ e' (Sum.inl z)) x.property)⟩
    continuous_toFun := by fun_prop }
  have hk : IsEmbedding k := IsEmbedding.subtypeVal.of_comp_iff.mp
    ((leftEnd_isEmbedding f g sq).comp IsEmbedding.subtypeVal)
  apply hk.toHomeomorphOfSurjective
  intro x
  have hx : height f g sq x.val = 0 := by
    rw [← height_map sq sq' a b c wf wg x.val,x.property,height_left]
  obtain ⟨z,hz⟩ := height_eq_zero_range f g sq x.val hx
  have hb : b z = y := (leftEnd_isEmbedding f' g' sq').injective
    ((map_left sq sq' a b c wf wg z).symm.trans ((congrArg (map sq sq' a b c wf wg) hz).trans
      x.property))
  exact ⟨⟨z,hb⟩,Subtype.ext hz⟩

/-- The right endpoint fiber is likewise unchanged. -/
def rightEndFiberHomeomorph (y : C') :
    {x : C // c x = y} ≃ₜ {x : D // map sq sq' a b c wf wg x = e' (Sum.inr y)} := by
  let k : C({x : C // c x = y},{x : D // map sq sq' a b c wf wg x = e' (Sum.inr y)}) := {
    toFun x := ⟨e (Sum.inr x.val),(map_right sq sq' a b c wf wg x.val).trans
      (congrArg (fun z ↦ e' (Sum.inr z)) x.property)⟩
    continuous_toFun := by fun_prop }
  have hk : IsEmbedding k := IsEmbedding.subtypeVal.of_comp_iff.mp
    ((rightEnd_isEmbedding f g sq).comp IsEmbedding.subtypeVal)
  apply hk.toHomeomorphOfSurjective
  intro x
  have hx : height f g sq x.val = 1 := by
    rw [← height_map sq sq' a b c wf wg x.val,x.property,height_right]
  obtain ⟨z,hz⟩ := height_eq_one_range f g sq x.val hx
  have hc : c z = y := (rightEnd_isEmbedding f' g' sq').injective
    ((map_right sq sq' a b c wf wg z).symm.trans ((congrArg (map sq sq' a b c wf wg) hz).trans
      x.property))
  exact ⟨⟨z,hc⟩,Subtype.ext hz⟩

/-- Every interior fiber is the original attaching-object fiber at the same height. -/
def interiorFiberHomeomorph (y : A') (t : OpenInterval) :
    {x : A // a x = y} ≃ₜ {x : D // map sq sq' a b c wf wg x = l' (y,ULift.up t.val)} := by
  let k : C({x : A // a x = y},{x : D // map sq sq' a b c wf wg x = l' (y,ULift.up t.val)}) := {
    toFun x := ⟨l (x.val,ULift.up t.val),(map_cylinder_apply sq sq' a b c wf wg x.val _).trans
      (congrArg (fun z ↦ l' (z,ULift.up t.val)) x.property)⟩
    continuous_toFun := by fun_prop }
  have hk : IsEmbedding k := IsEmbedding.subtypeVal.of_comp_iff.mp
    ((interior_isOpenEmbedding f g sq).isEmbedding.comp
      ((isEmbedding_prodMkLeft t).comp IsEmbedding.subtypeVal))
  apply hk.toHomeomorphOfSurjective
  intro x
  have hx : height f g sq x.val = t.val := by
    rw [← height_map sq sq' a b c wf wg x.val,x.property,height_cylinder]
  obtain ⟨z,hz⟩ := interior_surjective f g sq x.val (by rw [hx]; exact t.property)
  have hh : (a z.1,z.2) = (y,t) := (interior_isOpenEmbedding f' g' sq').injective
    ((map_cylinder_apply sq sq' a b c wf wg z.1 _).symm.trans
      ((congrArg (map sq sq' a b c wf wg) hz).trans x.property))
  have ha : a z.1 = y := congrArg Prod.fst hh
  have ht : z.2 = t := congrArg Prod.snd hh
  refine ⟨⟨z.1,ha⟩,Subtype.ext ?_⟩
  change l (z.1,ULift.up t.val) = x.val
  exact (congrArg (fun s : OpenInterval ↦ l (z.1,ULift.up s.val)) ht.symm).trans hz

@[simp] theorem leftEndFiberHomeomorph_val (y : B') (x : {x : B // b x = y}) :
    (leftEndFiberHomeomorph sq sq' a b c wf wg y x).val = e (Sum.inl x.val) := rfl
@[simp] theorem rightEndFiberHomeomorph_val (y : C') (x : {x : C // c x = y}) :
    (rightEndFiberHomeomorph sq sq' a b c wf wg y x).val = e (Sum.inr x.val) := rfl
@[simp] theorem interiorFiberHomeomorph_val (y : A') (t : OpenInterval) (x : {x : A // a x = y}) :
    (interiorFiberHomeomorph sq sq' a b c wf wg y t x).val = l (x.val,ULift.up t.val) := rfl

end Quillen.DoubleCylinder
