/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.Algebra.Homology.HomotopyPushout.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.CommSq

/-! # Actual weak-leg contraction and homotopy-pushout descent -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.CochainComplex
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- An epic exact biproduct cokernel gives the original actual pushout. -/
lemma isPushout_cokernel_biprod {T A B X : C} (f : T ⟶ A) (g : T ⟶ B) (k : A ⊞ B ⟶ X)
    (w : biprod.lift f (-g) ≫ k = 0)
    (hex : (ShortComplex.mk (biprod.lift f (-g)) k w).Exact) [Epi k] :
    IsPushout f g (biprod.inl ≫ k) (biprod.inr ≫ k) := by
  have hk : biprod.desc (biprod.inl ≫ k) (biprod.inr ≫ k) = k := by
    apply biprod.hom_ext' <;> simp
  have hw : f ≫ (biprod.inl ≫ k) = g ≫ (biprod.inr ≫ k) := by
    apply sub_eq_zero.mp
    calc
      f ≫ (biprod.inl ≫ k) - g ≫ (biprod.inr ≫ k) =
          biprod.lift f (-g) ≫ biprod.desc (biprod.inl ≫ k) (biprod.inr ≫ k) := by
        simp only [biprod.lift_desc, Preadditive.neg_comp, sub_eq_add_neg]
      _ = 0 := by rw [hk, w]
  let sq : CommSq f g (biprod.inl ≫ k) (biprod.inr ≫ k) := ⟨hw⟩
  have hcok : IsColimit sq.cokernelCofork := by
    simpa only [CommSq.cokernelCofork, hk] using hex.gIsCokernel
  exact IsPushout.of_isColimit (sq.isColimitEquivIsColimitCokernelCofork.symm hcok)

variable {T A B : CochainComplex C ℤ} (f : T ⟶ A) (g : T ⟶ B)

/-- A weak second leg makes the actual overlap difference monic on homology. -/
lemma mono_homologyMap_biprod_lift_of_quasiIso [QuasiIso g] (n : ℤ) :
    Mono (homologyMap (biprod.lift f (-g)) n) := by
  have : IsIso (homologyMap (-g) n) := by
    rw [homologyMap_neg]
    exact (-asIso (homologyMap g n)).isIso_hom
  have h : homologyMap (biprod.lift f (-g)) n ≫
      homologyMap (biprod.snd : A ⊞ B ⟶ B) n = homologyMap (-g) n := by
    rw [← homologyMap_comp, biprod.lift_snd]
  exact mono_of_mono_fac h

/-- Injectivity in the next degree makes the actual homology square a pushout. -/
lemma homology_homotopyPushout_isPushout (n : ℤ)
    [Mono (homologyMap (biprod.lift f (-g)) (n + 1))] :
    IsPushout (homologyMap f n) (homologyMap g n)
      (homologyMap (homotopyPushoutInl f g) n) (homologyMap (homotopyPushoutInr f g) n) := by
  let : HasDerivedCategory C := HasDerivedCategory.standard _
  let φ := biprod.lift f (-g)
  let T₀ := CochainComplex.mappingCone.triangle φ
  have hT := DerivedCategory.mappingCone_triangle_distinguished φ
  let H := homologyFunctor C (.up ℤ) n
  have hδ : CochainComplex.homologyδOfTriangle T₀ n (n + 1) rfl = 0 := by
    apply (cancel_mono (homologyMap φ (n + 1))).mp
    simpa only [zero_comp, T₀, CochainComplex.mappingCone.triangle_mor₁] using
      CochainComplex.homologyδOfTriangle_homologyMap T₀ hT n (n + 1) rfl
  have hepi : Epi (homologyMap T₀.mor₂ n) :=
    (CochainComplex.homologyMap_exact₃_of_distTriang T₀ hT n (n + 1) rfl).epi_f hδ
  have hex := CochainComplex.homologyMap_exact₂_of_distTriang T₀ hT n
  let : PreservesBinaryBiproducts H := preservesBinaryBiproducts_of_preservesBinaryProducts H
  let e := H.mapBiprod A B
  let k := e.inv ≫ homologyMap T₀.mor₂ n
  have he : biprod.lift (H.map f) (-H.map g) ≫ e.inv = H.map φ := by
    simpa only [Functor.map_neg] using biprod.lift_mapBiprod H A B f (-g)
  have w : biprod.lift (H.map f) (-H.map g) ≫ k = 0 := by
    rw [← Category.assoc, he]
    exact CochainComplex.homologyMap_comp_eq_zero_of_distTriang T₀ hT n
  have hx : (ShortComplex.mk (biprod.lift (H.map f) (-H.map g)) k w).Exact := by
    apply ShortComplex.exact_of_iso _ hex
    refine ShortComplex.isoMk (Iso.refl _) e (Iso.refl _) ?_ ?_
    · simpa only [T₀, H, φ, e, CochainComplex.mappingCone.triangle_mor₁,
        CochainComplex.mappingCone.triangle_obj₁, Iso.refl_hom, Category.id_comp,
        homologyFunctor_map, homologyMap_neg, Functor.map_neg] using
        (biprod.map_lift_mapBiprod H A B f (-g)).symm
    · simp [k]
  have : Epi k := by dsimp [k]; infer_instance
  have hi := isPushout_cokernel_biprod (H.map f) (H.map g) k w hx
  have hk : biprod.inl ≫ k = homologyMap (homotopyPushoutInl f g) n := by
    dsimp only [k]
    rw [← Category.assoc]
    change (biprod.inl ≫ e.inv) ≫ H.map T₀.mor₂ = H.map (homotopyPushoutInl f g)
    dsimp only [e]
    rw [Functor.mapBiprod_inv, biprod.inl_desc, ← H.map_comp]
    rfl
  have hk' : biprod.inr ≫ k = homologyMap (homotopyPushoutInr f g) n := by
    dsimp only [k]
    rw [← Category.assoc]
    change (biprod.inr ≫ e.inv) ≫ H.map T₀.mor₂ = H.map (homotopyPushoutInr f g)
    dsimp only [e]
    rw [Functor.mapBiprod_inv, biprod.inr_desc, ← H.map_comp]
    rfl
  simpa only [hk, hk', H, homologyFunctor_map] using hi

/-- The original first inclusion is weak if the second overlap arrow is weak. -/
lemma quasiIso_homotopyPushoutInl [QuasiIso g] : QuasiIso (homotopyPushoutInl f g) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have := mono_homologyMap_biprod_lift_of_quasiIso f g (n + 1)
  exact (homology_homotopyPushout_isPushout f g n).isIso_inl_of_isIso

/-- The original second inclusion is weak if the first overlap arrow is weak. -/
lemma quasiIso_homotopyPushoutInr [QuasiIso f] : QuasiIso (homotopyPushoutInr f g) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have : Mono (homologyMap (biprod.lift f (-g)) (n + 1)) := by
    apply mono_of_mono_fac (show homologyMap (biprod.lift f (-g)) (n + 1) ≫
      homologyMap (biprod.fst : A ⊞ B ⟶ A) (n + 1) = homologyMap f (n + 1) from ?_)
    rw [← homologyMap_comp, biprod.lift_fst]
  exact (homology_homotopyPushout_isPushout f g n).isIso_inr_of_isIso

/-- Descent remains weak from an actual weak overlap leg and weak first component. -/
lemma quasiIso_homotopyPushoutDesc {M : CochainComplex C ℤ}
    (a : A ⟶ M) (b : B ⟶ M) (H : Homotopy (f ≫ a) (g ≫ b))
    [QuasiIso g] [QuasiIso a] : QuasiIso (homotopyPushoutDesc f g a b H) := by
  have := quasiIso_homotopyPushoutInl f g
  have : QuasiIso (homotopyPushoutInl f g ≫ homotopyPushoutDesc f g a b H) := by
    rw [homotopyPushoutInl_desc]
    infer_instance
  exact (quasiIso_iff_comp_left (homotopyPushoutInl f g)
    (homotopyPushoutDesc f g a b H)).mp inferInstance

/-- The symmetric weak descent assertion uses the literal second leg equation. -/
lemma quasiIso_homotopyPushoutDesc_of_inr {M : CochainComplex C ℤ}
    (a : A ⟶ M) (b : B ⟶ M) (H : Homotopy (f ≫ a) (g ≫ b))
    [QuasiIso f] [QuasiIso b] : QuasiIso (homotopyPushoutDesc f g a b H) := by
  have := quasiIso_homotopyPushoutInr f g
  have : QuasiIso (homotopyPushoutInr f g ≫ homotopyPushoutDesc f g a b H) := by
    rw [homotopyPushoutInr_desc]
    infer_instance
  exact (quasiIso_iff_comp_left (homotopyPushoutInr f g)
    (homotopyPushoutDesc f g a b H)).mp inferInstance

end Quillen.CochainComplex
