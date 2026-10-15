/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.CategoryTheory.ExactCategory.SpecialFractions
public import Quillen.KTheory.Map.CoherenceData
public import Mathlib.CategoryTheory.Core

/-!
# The core of an exact Q-category

A Q-isomorphism has invertible legs in every admissible-span representative.
Consequently the ordinary isomorphisms of the original exact category map
bijectively to Q-isomorphisms, giving an equivalence of cores. The proof uses
admissibility and an actual splitting, not balancedness of the exact category.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ExactCategory.ExactStructure
open Quillen
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- Every representative of an invertible Q-arrow has two invertible legs. -/
theorem qSpan_isIso_legs {X Y : C} (s : Span E.deflation E.inflation X Y)
    [IsIso (Q.mkHom _ _ s)] : IsIso s.l ∧ IsIso s.r := by
  obtain ⟨t, ht⟩ := Quotient.exists_rep (inv (Q.mkHom _ _ s))
  change Span E.deflation E.inflation Y X at t
  change Q.mkHom _ _ t = inv (Q.mkHom _ _ s) at ht
  have h₁ : Q.mkHom _ _ (Span.comp s t) = Q.mkHom _ _ (Span.id X) := by
    change Q.mkHom _ _ s ≫ Q.mkHom _ _ t = 𝟙 _
    rw [ht]
    exact IsIso.hom_inv_id _
  have h₂ : Q.mkHom _ _ (Span.comp t s) = Q.mkHom _ _ (Span.id Y) := by
    change Q.mkHom _ _ t ≫ Q.mkHom _ _ s = 𝟙 _
    rw [ht]
    exact IsIso.inv_hom_id _
  obtain ⟨e₁, hl₁, _⟩ := (Q.mkHom_eq_iff_apexIso _ _ _ _).1 h₁
  obtain ⟨e₂, _, hr₂⟩ := (Q.mkHom_eq_iff_apexIso _ _ _ _).1 h₂
  have hl : pullback.fst s.r t.l ≫ s.l = e₁.hom := by simpa [Span.comp] using hl₁.symm
  have hr : pullback.snd t.r s.l ≫ s.r = e₂.hom := by simpa [Span.comp] using hr₂.symm
  have : Mono (pullback.fst s.r t.l) := mono_of_mono_fac hl
  have hp : E.deflation (pullback.fst s.r t.l) :=
    E.deflation.pullback_fst s.r t.l t.wl
  have : IsIso (pullback.fst s.r t.l) := E.isIso_of_deflation_of_mono _ hp
  have : IsIso (pullback.fst s.r t.l ≫ s.l) := by rw [hl]; infer_instance
  have hleft : IsIso s.l := IsIso.of_isIso_comp_left (pullback.fst s.r t.l) s.l
  have : Mono s.r := E.mono_of_inflation s.wr
  have : IsSplitEpi s.r := IsSplitEpi.mk'
    { section_ := e₂.inv ≫ pullback.snd t.r s.l
      id := by rw [Category.assoc, hr]; simp }
  exact ⟨hleft, isIso_of_mono_of_isSplitEpi s.r⟩

/-- An admissible span with invertible legs represents the original isomorphism. -/
theorem qSpan_eq_qIsoOfIso {X Y : C} (s : Span E.deflation E.inflation X Y)
    [IsIso s.l] [IsIso s.r] :
    Q.mkHom _ _ s = (E.qIsoOfIso ((asIso s.l).symm ≪≫ asIso s.r)).hom := by
  apply Q.mkHom_eq_of_apexIso _ _ s _ (asIso s.l)
  · simp [Q.isoSpan]
  · simp [Q.isoSpan]

/-- Equality of Q-isomorphisms induced from ordinary isomorphisms detects
exactly equality of the original isomorphisms. -/
theorem qIsoOfIso_injective {X Y : C} :
    Function.Injective (E.qIsoOfIso : (X ≅ Y) → _) := by
  intro e f h
  have hhom := congrArg Iso.hom h
  change Q.mkHom _ _ (Q.isoSpan _ _ e _) = Q.mkHom _ _ (Q.isoSpan _ _ f _) at hhom
  obtain ⟨a, hl, hr⟩ := (Q.mkHom_eq_iff_apexIso _ _ _ _).1 hhom
  have ha : a.hom = 𝟙 X := by simpa [Q.isoSpan] using hl
  apply Iso.ext
  simpa [Q.isoSpan, ha] using hr.symm

/-- Every invertible Q-arrow comes from a genuine original isomorphism. -/
theorem exists_iso_of_qHom_isIso {X Y : C}
    (f : Q.of E.deflation E.inflation X ⟶ Q.of E.deflation E.inflation Y)
    [IsIso f] : ∃ e : X ≅ Y, (E.qIsoOfIso e).hom = f := by
  obtain ⟨s, hs⟩ := Quotient.exists_rep f
  change Span E.deflation E.inflation X Y at s
  change Q.mkHom _ _ s = f at hs
  have : IsIso (Q.mkHom _ _ s) := by rw [hs]; infer_instance
  obtain ⟨hl, hr⟩ := E.qSpan_isIso_legs s
  let := hl
  let := hr
  exact ⟨(asIso s.l).symm ≪≫ asIso s.r, (E.qSpan_eq_qIsoOfIso s).symm.trans hs⟩

/-- Ordinary isomorphisms and Q-isomorphisms correspond bijectively. -/
theorem qIsoOfIso_bijective {X Y : C} :
    Function.Bijective (E.qIsoOfIso : (X ≅ Y) → _) := by
  refine ⟨E.qIsoOfIso_injective, ?_⟩
  intro f
  obtain ⟨e, he⟩ := E.exists_iso_of_qHom_isIso f.hom
  exact ⟨e, Iso.ext he⟩

/-- The identity-on-objects functor from original isomorphisms to Q-isomorphisms. -/
def qCoreFunctor : Core C ⥤ Core (Q E.deflation E.inflation) where
  obj X := ⟨Q.of E.deflation E.inflation X.of⟩
  map f := ⟨E.qIsoOfIso f.iso⟩
  map_id X := by apply CoreHom.ext; apply Iso.ext; rfl
  map_comp f g := by apply CoreHom.ext; exact E.qIsoOfIso_trans f.iso g.iso

instance qCoreFunctor_faithful : (E.qCoreFunctor).Faithful where
  map_injective h := CoreHom.ext (E.qIsoOfIso_injective (congrArg CoreHom.iso h))

instance qCoreFunctor_full : (E.qCoreFunctor).Full where
  map_surjective f := by
    obtain ⟨e, he⟩ := E.qIsoOfIso_bijective.surjective f.iso
    exact ⟨⟨e⟩, CoreHom.ext he⟩

instance qCoreFunctor_essSurj : (E.qCoreFunctor).EssSurj where
  mem_essImage X := ⟨⟨X.of.obj.of⟩, ⟨Core.isoMk (Iso.refl _)⟩⟩

instance qCoreFunctor_isEquivalence : (E.qCoreFunctor).IsEquivalence where

/-- The equivalence retains precisely the original `qIsoOfIso` on every arrow. -/
def qCoreEquivalence : Core C ≌ Core (Q E.deflation E.inflation) :=
  (E.qCoreFunctor).asEquivalence

@[simp]
theorem qCoreEquivalence_map {X Y : Core C} (f : X ⟶ Y) :
    ((E.qCoreEquivalence).functor.map f).iso = E.qIsoOfIso f.iso := rfl

end CategoryTheory.ExactCategory.ExactStructure
