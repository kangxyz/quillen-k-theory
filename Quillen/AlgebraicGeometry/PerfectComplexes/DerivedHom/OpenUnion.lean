/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedHom.MayerVietoris
public import Quillen.AlgebraicGeometry.PerfectComplexes.HomologyCover

/-! # Derived Hom on original open unions -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u v
namespace Quillen

/-- Transport of actual Hom vanishing through the displayed original isomorphisms. -/
theorem hom_eq_zero_of_iso {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {A B A' B' : C} (eA : A ≅ A') (eB : B ≅ B')
    (h : ∀ f : A' ⟶ B', f = 0) (f : A ⟶ B) : f = 0 := by
  have hf := h (eA.inv ≫ f ≫ eB.hom)
  apply (cancel_epi eA.inv).mp
  apply (cancel_mono eB.hom).mp
  simpa only [Category.assoc, zero_comp, comp_zero] using hf

namespace PerfectComplexes
attribute [local instance] HasDerivedCategory.standard

/-- Arbitrary actual covering open immersions detect original quasi-isomorphisms. -/
theorem quasiIso_of_openImmersionCover {X : Scheme.{u}} {K L : Complex X} (f : K ⟶ L)
    {ι : Type v} (Y : ι → Scheme.{u}) (j : ∀ i, Y i ⟶ X)
    [∀ i, IsOpenImmersion (j i)] (hj : ∀ x : X, ∃ i, ∃ y : Y i, j i y = x)
    (hf : ∀ i, QuasiIso ((restrict (j i)).map f)) : QuasiIso f := by
  apply HomologicalAlgebra.quasiIso_of_mappingCone_acyclic
  intro n
  apply exactAt_of_openImmersionCover _ Y j hj n
  intro i
  let := hf i
  exact (mappingCone_acyclic_of_quasiIso ((restrict (j i)).map f) n).of_iso
    (CochainComplex.mappingCone.mapHomologicalComplexIso f (Scheme.Modules.restrictFunctor (j
      i))).symm

open OpenHomotopyGluing
/-- The actual geometric two-open resolution supplies a full Hom-vanishing
criterion for any covering cartesian open square. -/
theorem derivedHom_eq_zero_of_openSquare
    {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (j : U ⟶ X) (k : V ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion j] [IsOpenImmersion k]
    (h : a ≫ j = b ≫ k)
    (hja : ∀ x : U, j x ∈ Set.range k → x ∈ Set.range a)
    (hkb : ∀ x : V, k x ∈ Set.range j → x ∈ Set.range b)
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range k)
    (E L : Complex X)
    (hU : ∀ φ : (toDerived U).obj ((restrict j).obj E) ⟶
      (toDerived U).obj ((restrict j).obj L), φ = 0)
    (hV : ∀ φ : (toDerived V).obj ((restrict k).obj E) ⟶
      (toDerived V).obj ((restrict k).obj L), φ = 0)
    (hW : ∀ φ : ((toDerived W).obj ((restrict a).obj ((restrict j).obj E)))⟦(1 : ℤ)⟧ ⟶
      (toDerived W).obj ((restrict a).obj ((restrict j).obj L)), φ = 0)
    (φ : (toDerived X).obj E ⟶ (toDerived X).obj L) : φ = 0 := by
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
  have hz : (toDerived X).map d ≫ φ = 0 :=
    derivedHom_glued_eq_zero a b j k h α β L hU hV hW _
  apply (cancel_epi ((toDerived X).map d)).mp
  simpa only [comp_zero] using hz

/-- The actual restriction-composition isomorphism for an inclusion of opens. -/
def restrictOpenInclusionIso {X : Scheme.{u}} {U V : X.Opens} (h : U ≤ V) (E : Complex X) :
    (restrict (X.homOfLE h)).obj ((restrict V.ι).obj E) ≅ (restrict U.ι).obj E :=
  (restrictCompIso (X.homOfLE h) V.ι).app E ≪≫
    (eqToIso (restrict_congr (Scheme.homOfLE_ι X h))).app E

/-- Actual unshifted Hom vanishing on an open union, with the genuine shifted
intersection obstruction. No affine or perfect hypotheses are needed. -/
theorem derivedHom_eq_zero_on_openUnion {X : Scheme.{u}} (E L : Complex X) (U V : X.Opens)
    (hU : ∀ φ : (toDerived U.toScheme).obj ((restrict U.ι).obj E) ⟶
      (toDerived U.toScheme).obj ((restrict U.ι).obj L), φ = 0)
    (hV : ∀ φ : (toDerived V.toScheme).obj ((restrict V.ι).obj E) ⟶
      (toDerived V.toScheme).obj ((restrict V.ι).obj L), φ = 0)
    (hW : ∀ φ : ((toDerived (U ⊓ V).toScheme).obj ((restrict (U ⊓ V).ι).obj E))⟦(1 : ℤ)⟧ ⟶
      (toDerived (U ⊓ V).toScheme).obj ((restrict (U ⊓ V).ι).obj L), φ = 0)
    (φ : (toDerived (U ⊔ V).toScheme).obj ((restrict (U ⊔ V).ι).obj E) ⟶
      (toDerived (U ⊔ V).toScheme).obj ((restrict (U ⊔ V).ι).obj L)) : φ = 0 := by
  let a := X.homOfLE (inf_le_left : U ⊓ V ≤ U)
  let b := X.homOfLE (inf_le_right : U ⊓ V ≤ V)
  let j := X.homOfLE (le_sup_left : U ≤ U ⊔ V)
  let k := X.homOfLE (le_sup_right : V ≤ U ⊔ V)
  have h : a ≫ j = b ≫ k := by simp [a, b, j, k]
  apply derivedHom_eq_zero_of_openSquare a b j k h _ _ _
    ((restrict (U ⊔ V).ι).obj E) ((restrict (U ⊔ V).ι).obj L) _ _ _ φ
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
  · exact hom_eq_zero_of_iso
      ((toDerived U.toScheme).mapIso (restrictOpenInclusionIso (le_sup_left : U ≤ U ⊔ V) E))
      ((toDerived U.toScheme).mapIso (restrictOpenInclusionIso (le_sup_left : U ≤ U ⊔ V) L)) hU
  · exact hom_eq_zero_of_iso
      ((toDerived V.toScheme).mapIso (restrictOpenInclusionIso le_sup_right E))
      ((toDerived V.toScheme).mapIso (restrictOpenInclusionIso le_sup_right L)) hV
  · let eE := (restrict a).mapIso (restrictOpenInclusionIso (le_sup_left : U ≤ U ⊔ V) E) ≪≫
        restrictOpenInclusionIso inf_le_left E
    let eL := (restrict a).mapIso (restrictOpenInclusionIso (le_sup_left : U ≤ U ⊔ V) L) ≪≫
        restrictOpenInclusionIso inf_le_left L
    exact hom_eq_zero_of_iso
      ((shiftFunctor (Derived (U ⊓ V).toScheme) (1 : ℤ)).mapIso
        ((toDerived (U ⊓ V).toScheme).mapIso eE))
      ((toDerived (U ⊓ V).toScheme).mapIso eL) hW

end PerfectComplexes
end Quillen
