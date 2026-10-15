/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedHom.OpenUnion


/-!
# Genuine finite-cover derived nilpotence

An original derived map which vanishes on both pieces of a binary open cover,
followed by a map vanishing on the first piece, has zero composite. The proof
uses the actual extension-by-zero cone resolution: the first map factors
through its shifted overlap and the genuine shifted adjunction kills the
composite. No perfectness, quasicoherence, or boundedness is assumed.

Consequently an actual chain endomorphism which is derived-nilpotent on each
member of a finite open family is derived-nilpotent on their union. The
conclusion retains a power of the original chain map. Local nullity is not
mistaken for global nullity; the Mayer–Vietoris step raises the exponent.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
  HomologicalComplex
universe u v w
namespace Quillen.CochainComplex
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
attribute [local instance] Abelian.hasFiniteBiproducts

/-- The original cone triangle factors a map killed by both inclusions. -/
theorem derivedHom_homotopyPushout_comp_eq_zero
    {T A B : CochainComplex C ℤ} (f : T ⟶ A) (g : T ⟶ B)
    {L M : DerivedCategory C}
    (φ : DerivedCategory.Q.obj (homotopyPushout f g) ⟶ L) (ψ : L ⟶ M)
    (hA : DerivedCategory.Q.map (homotopyPushoutInl f g) ≫ φ = 0)
    (hB : DerivedCategory.Q.map (homotopyPushoutInr f g) ≫ φ = 0)
    (hT : ∀ γ : (DerivedCategory.Q.obj T)⟦(1 : ℤ)⟧ ⟶ L, γ ≫ ψ = 0) :
    φ ≫ ψ = 0 := by
  let d := biprod.lift f (-g)
  have hm : DerivedCategory.Q.map (CochainComplex.mappingCone.inr d) ≫ φ = 0 := by
    have he : (biprod.fst : A ⊞ B ⟶ A) ≫ homotopyPushoutInl f g +
        (biprod.snd : A ⊞ B ⟶ B) ≫ homotopyPushoutInr f g =
        CochainComplex.mappingCone.inr d := by
      simp only [homotopyPushoutInl, homotopyPushoutInr, ← Category.assoc,
        ← Preadditive.add_comp, biprod.total, Category.id_comp, d]
    rw [← he, Functor.map_add, Preadditive.add_comp, Functor.map_comp,
      Functor.map_comp, Category.assoc, Category.assoc, hA, hB, comp_zero, comp_zero, add_zero]
  obtain ⟨γ, hγ⟩ := Triangle.yoneda_exact₃ _
    (DerivedCategory.mappingCone_triangle_distinguished d) φ hm
  rw [hγ, Category.assoc, hT γ, comp_zero]
end Quillen.CochainComplex

namespace Quillen.PerfectComplexes.OpenHomotopyGluing
attribute [local instance] HasDerivedCategory.standard
open Quillen.CochainComplex
variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (j : U ⟶ X) (k : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion j] [IsOpenImmersion k]
  (h : a ≫ j = b ≫ k)
  {K : Complex W} {A : Complex U} {B : Complex V}
  (α : K ⟶ (restrict a).obj A) (β : K ⟶ (restrict b).obj B)

/-- A map locally zero on both pieces followed by a map zero on the first
piece is zero on the genuine original cone glue. -/
theorem derivedHom_glued_comp_eq_zero {L M : Complex X}
    (φ : (toDerived X).obj (glued a b j k h α β) ⟶ (toDerived X).obj L)
    (ψ : (toDerived X).obj L ⟶ (toDerived X).obj M)
    (hj : restrictDerivedHom j φ = 0) (hk : restrictDerivedHom k φ = 0)
    (hψ : restrictDerivedHom j ψ = 0) : φ ≫ ψ = 0 := by
  refine derivedHom_homotopyPushout_comp_eq_zero (left a j α) (right a b j k h β) φ ψ ?_ ?_ ?_
  · apply (extensionByZeroDerivedHomEquiv_eq_zero_iff j A L _).mp
    rw [extensionByZeroDerivedHomEquiv_postcomp, hj, comp_zero]
  · apply (extensionByZeroDerivedHomEquiv_eq_zero_iff k B L _).mp
    rw [extensionByZeroDerivedHomEquiv_postcomp, hk, comp_zero]
  · intro γ
    apply (extensionByZeroDerivedShiftHomEquiv_eq_zero_iff j ((extensionByZero a).obj K) M 1 _).mp
    rw [extensionByZeroDerivedShiftHomEquiv_postcomp, hψ, comp_zero]
end Quillen.PerfectComplexes.OpenHomotopyGluing

namespace Quillen.PerfectComplexes
attribute [local instance] HasDerivedCategory.standard
open OpenHomotopyGluing

/-- Original derived maps locally zero on a binary cover compose to zero.
The second map need only vanish on the first covering open. -/
theorem derivedHom_comp_eq_zero_of_openSquare
    {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (j : U ⟶ X) (k : V ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion j] [IsOpenImmersion k]
    (h : a ≫ j = b ≫ k)
    (hja : ∀ x : U, j x ∈ Set.range k → x ∈ Set.range a)
    (hkb : ∀ x : V, k x ∈ Set.range j → x ∈ Set.range b)
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range k)
    {E L M : Complex X}
    (φ : (toDerived X).obj E ⟶ (toDerived X).obj L)
    (ψ : (toDerived X).obj L ⟶ (toDerived X).obj M)
    (hU : restrictDerivedHom j φ = 0) (hV : restrictDerivedHom k φ = 0)
    (hψ : restrictDerivedHom j ψ = 0) : φ ≫ ψ = 0 := by
  let e := openSquareRestrictIso b a k j h.symm
  let K := (restrict a).obj ((restrict j).obj E)
  let α : K ⟶ (restrict a).obj ((restrict j).obj E) := 𝟙 _
  let β : K ⟶ (restrict b).obj ((restrict k).obj E) := e.inv.app E
  let H : Homotopy (α ≫ (restrict a).map (𝟙 ((restrict j).obj E)))
      (β ≫ (restrict b).map (𝟙 ((restrict k).obj E)) ≫ e.hom.app E) :=
    Homotopy.ofEq (by simp [α, β, K])
  let d := desc a b j k h α β (𝟙 _) (𝟙 _) H
  let Y : Bool → Scheme := fun t => if t then U else V
  let q : ∀ t, Y t ⟶ X := fun t => by
    cases t with
    | false => exact k
    | true => exact j
  have : ∀ t, IsOpenImmersion (q t) := by intro t; cases t <;> dsimp [q] <;> infer_instance
  have hd : QuasiIso d := by
    apply quasiIso_of_openImmersionCover d Y q
    · intro x
      rcases hcover x with ⟨y, hy⟩ | ⟨y, hy⟩
      · exact ⟨true, y, hy⟩
      · exact ⟨false, y, hy⟩
    · intro t
      cases t with
      | false => exact desc_restrict_second_quasiIso a b j k h α β (𝟙 _) (𝟙 _) H hkb
      | true => exact desc_restrict_first_quasiIso a b j k h α β (𝟙 _) (𝟙 _) H hja
  have hz : ((toDerived X).map d ≫ φ) ≫ ψ = 0 := by
    apply derivedHom_glued_comp_eq_zero a b j k h α β
    · rw [restrictDerivedHom_comp, hU, comp_zero]
    · rw [restrictDerivedHom_comp, hV, comp_zero]
    · exact hψ
  apply (cancel_epi ((toDerived X).map d)).mp
  simpa only [Category.assoc, comp_zero] using hz
end Quillen.PerfectComplexes

namespace Quillen.PerfectComplexes
attribute [local instance] HasDerivedCategory.standard

/-- Zero of an original chain map is unchanged by the actual composition
comparison for inclusions of opens. -/
lemma toDerived_restrict_openInclusion_eq_zero_iff {X : Scheme.{u}}
    {U V : X.Opens} (h : U ≤ V) {E L : Complex X} (f : E ⟶ L) :
    (toDerived U.toScheme).map ((restrict (X.homOfLE h)).map ((restrict V.ι).map f)) = 0 ↔
      (toDerived U.toScheme).map ((restrict U.ι).map f) = 0 := by
  let e := restrictCompIso (X.homOfLE h) V.ι ≪≫
    (eqToIso (restrict_congr (Scheme.homOfLE_ι X h)))
  have hn := congrArg ((toDerived U.toScheme).map) (e.hom.naturality f)
  simp only [Functor.map_comp, Functor.comp_map] at hn
  constructor
  · intro hf
    rw [hf, zero_comp] at hn
    apply (cancel_epi ((toDerived U.toScheme).map (e.hom.app E))).mp
    simpa only [comp_zero] using hn.symm
  · intro hf
    rw [hf, comp_zero] at hn
    apply (cancel_mono ((toDerived U.toScheme).map (e.hom.app L))).mp
    simpa only [zero_comp] using hn

/-- The literal original maps on a union obey the genuine MV composition
criterion. No perfectness, compactness or cohomology bounds are needed. -/
theorem toDerived_restrict_comp_eq_zero_on_openUnion {X : Scheme.{u}}
    {E L M : Complex X} (f : E ⟶ L) (g : L ⟶ M) (U V : X.Opens)
    (hU : (toDerived U.toScheme).map ((restrict U.ι).map f) = 0)
    (hV : (toDerived V.toScheme).map ((restrict V.ι).map f) = 0)
    (hψ : (toDerived U.toScheme).map ((restrict U.ι).map g) = 0) :
    (toDerived (U ⊔ V).toScheme).map ((restrict (U ⊔ V).ι).map (f ≫ g)) = 0 := by
  let a := X.homOfLE (inf_le_left : U ⊓ V ≤ U)
  let b := X.homOfLE (inf_le_right : U ⊓ V ≤ V)
  let j := X.homOfLE (le_sup_left : U ≤ U ⊔ V)
  let k := X.homOfLE (le_sup_right : V ≤ U ⊔ V)
  have h : a ≫ j = b ≫ k := by simp [a, b, j, k]
  rw [Functor.map_comp, Functor.map_comp]
  apply derivedHom_comp_eq_zero_of_openSquare a b j k h
  · intro x hx
    obtain ⟨y, hy⟩ := hx
    refine ⟨⟨x.val, x.property, ?_⟩, ?_⟩
    · have he := congrArg Subtype.val hy
      simp only [j, k, Scheme.homOfLE_apply] at he
      exact he ▸ y.property
    · apply Subtype.ext
      exact Scheme.homOfLE_apply _ _
  · intro x hx
    obtain ⟨y, hy⟩ := hx
    refine ⟨⟨x.val, ?_, x.property⟩, ?_⟩
    · have he := congrArg Subtype.val hy
      simp only [j, k, Scheme.homOfLE_apply] at he
      exact he ▸ y.property
    · apply Subtype.ext
      exact Scheme.homOfLE_apply _ _
  · intro x
    rcases x.property with hx | hx
    · exact Or.inl ⟨⟨x.val, hx⟩, by apply Subtype.ext; exact Scheme.homOfLE_apply _ _⟩
    · exact Or.inr ⟨⟨x.val, hx⟩, by apply Subtype.ext; exact Scheme.homOfLE_apply _ _⟩
  · rw [restrictDerivedHom_map]
    exact (toDerived_restrict_openInclusion_eq_zero_iff le_sup_left f).mpr hU
  · rw [restrictDerivedHom_map]
    exact (toDerived_restrict_openInclusion_eq_zero_iff le_sup_right f).mpr hV
  · rw [restrictDerivedHom_map]
    exact (toDerived_restrict_openInclusion_eq_zero_iff le_sup_left g).mpr hψ

/-- Actual derived nilpotence of an original chain endomorphism on an open. -/
def DerivedNilpotentOn {X : Scheme.{u}} {E : Complex X} (f : End E) (U : X.Opens) : Prop :=
  ∃ n : ℕ, (toDerived U.toScheme).map ((restrict U.ι).map (f ^ n)) = 0

lemma derivedNilpotentOn_union {X : Scheme.{u}} {E : Complex X} (f : End E) (U V : X.Opens)
    (hU : DerivedNilpotentOn f U) (hV : DerivedNilpotentOn f V) :
    DerivedNilpotentOn f (U ⊔ V) := by
  obtain ⟨n, hn⟩ := hU
  obtain ⟨m, hm⟩ := hV
  have hU' : (toDerived U.toScheme).map ((restrict U.ι).map (f ^ (n+m))) = 0 := by
    rw [pow_add, End.mul_def, Functor.map_comp, Functor.map_comp, hn, comp_zero]
  have hV' : (toDerived V.toScheme).map ((restrict V.ι).map (f ^ (n+m))) = 0 := by
    rw [pow_add, End.mul_def, Functor.map_comp, Functor.map_comp, hm, zero_comp]
  refine ⟨(n+m)+(n+m), ?_⟩
  rw [pow_add, End.mul_def]
  exact toDerived_restrict_comp_eq_zero_on_openUnion (f ^ (n+m)) (f ^ (n+m)) U V hU' hV' hU'

lemma derivedNilpotentOn_bot {X : Scheme.{u}} {E : Complex X} (f : End E) :
    DerivedNilpotentOn f ⊥ := by
  have hE : IsZero ((restrict (⊥ : X.Opens).ι).obj E) := by
    rw [IsZero.iff_id_eq_zero]
    ext i : 1
    have hz : IsZero (((restrict (⊥ : X.Opens).ι).obj E).X i) := by
      rw [AlgebraicGeometry.Scheme.Modules.isZero_iff_stalks]
      intro x
      exact False.elim x.property
    exact hz.eq_of_src _ _
  exact ⟨0, ((toDerived (⊥ : X.Opens).toScheme).map_isZero hE).eq_of_src _ _⟩

/-- Genuine finite-cover nilpotence; local nullity alone is never substituted
for global nullity. The finite MV induction supplies a new exponent. -/
lemma derivedNilpotentOn_finite_union {X : Scheme.{u}} {E : Complex X} (f : End E)
    (s : Finset X.Opens) (hs : ∀ U ∈ s, DerivedNilpotentOn f U) :
    DerivedNilpotentOn f (s.sup id) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using derivedNilpotentOn_bot f
  | @insert U s hUs ih =>
    rw [Finset.sup_insert, id_eq]
    exact derivedNilpotentOn_union f U (s.sup id) (hs U (Finset.mem_insert_self _ _))
      (ih (fun V hV => hs V (Finset.mem_insert_of_mem hV)))
end Quillen.PerfectComplexes
