/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.CategoryTheory.QConstruction.Abelian.Surjections

/-!
# Cospan representatives for abelian Q-arrows

The mono-epi cospan of an abelian Q-arrow is unique up to a commuting
isomorphism. This is obtained from the pushout universal property of its
pullback square, rather than from an additional quotient relation.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits

namespace Quillen
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- An abelian pullback along an epimorphism is also a pushout. -/
theorem isPushout_of_isPullback_epi {A B D E : C}
    {f : A ⟶ B} {g : A ⟶ D} {i : B ⟶ E} {j : D ⟶ E}
    (sq : IsPullback f g i j) [Epi j] : IsPushout f g i j := by
  exact (isPullback_of_isPushout_mono sq.flip.op).unop.flip

namespace Q

/-- The actual admissible pullback span of a mono-epi cospan. -/
def cospanSpan {X Y U : C} (i : X ⟶ U) (p : Y ⟶ U) [Mono i] [Epi p] :
    AbelianSpan X Y :=
  ⟨pullback i p, pullback.fst i p, pullback.snd i p,
    (abelianExactStructure_deflation_iff C _).2 inferInstance,
    (abelianExactStructure_inflation_iff C _).2 inferInstance⟩

@[simp]
theorem mkHom_cospanSpan {X Y U : C} (i : X ⟶ U) (p : Y ⟶ U)
    [Mono i] [Epi p] :
    mkHom _ _ (cospanSpan i p) = inflationArrow i ≫ surjectionArrow p := by
  unfold inflationArrow surjectionArrow
  rw [← mkHom_comp]
  refine mkHom_eq_of_apexIso _ _ _ _ ?_ ?_ ?_
  · exact Iso.refl (pullback i p)
  · simp [cospanSpan, Span.comp]
  · simp [cospanSpan, Span.comp]

/-- A map out of the codomain of a mono-epi cospan descends uniquely from
compatible maps on its legs. -/
def cospanDesc {X Y U V : C} (i : X ⟶ U) (p : Y ⟶ U) [Epi p]
    (a : X ⟶ V) (b : Y ⟶ V)
    (w : pullback.fst i p ≫ a = pullback.snd i p ≫ b) : U ⟶ V :=
  (isPushout_of_isPullback_epi (IsPullback.of_hasPullback i p)).desc a b w

@[reassoc (attr := simp)]
theorem cospanDesc_left {X Y U V : C} (i : X ⟶ U) (p : Y ⟶ U) [Epi p]
    (a : X ⟶ V) (b : Y ⟶ V)
    (w : pullback.fst i p ≫ a = pullback.snd i p ≫ b) :
    i ≫ cospanDesc i p a b w = a := by simp [cospanDesc]

@[reassoc (attr := simp)]
theorem cospanDesc_right {X Y U V : C} (i : X ⟶ U) (p : Y ⟶ U) [Epi p]
    (a : X ⟶ V) (b : Y ⟶ V)
    (w : pullback.fst i p ≫ a = pullback.snd i p ≫ b) :
    p ≫ cospanDesc i p a b w = b := by simp [cospanDesc]

/-- Equality of cospan arrows supplies a compatible codomain isomorphism. -/
theorem exists_cospanIso_of_eq {X Y U V : C}
    (i : X ⟶ U) (p : Y ⟶ U) (j : X ⟶ V) (q : Y ⟶ V)
    [Mono i] [Epi p] [Mono j] [Epi q]
    (h : inflationArrow i ≫ surjectionArrow p = inflationArrow j ≫ surjectionArrow q) :
    ∃ e : U ≅ V, i ≫ e.hom = j ∧ p ≫ e.hom = q := by
  rw [← mkHom_cospanSpan, ← mkHom_cospanSpan] at h
  obtain ⟨e, hl, hr⟩ := (mkHom_eq_iff_apexIso _ _ _ _).1 h
  change e.hom ≫ pullback.fst j q = pullback.fst i p at hl
  change e.hom ≫ pullback.snd j q = pullback.snd i p at hr
  have w : pullback.fst i p ≫ j = pullback.snd i p ≫ q := by
    rw [← hl, Category.assoc, pullback.condition, ← Category.assoc, hr]
  have w' : pullback.fst j q ≫ i = pullback.snd j q ≫ p := by
    apply (cancel_epi e.hom).1
    simp only [← Category.assoc, hl, hr]
    exact pullback.condition
  let a := cospanDesc i p j q w
  let b := cospanDesc j q i p w'
  refine ⟨⟨a, b, ?_, ?_⟩, cospanDesc_left _ _ _ _ _, cospanDesc_right _ _ _ _ _⟩
  · apply (cancel_epi p).1
    simp [a, b]
  · apply (cancel_epi q).1
    simp [a, b]

/-- A commuting codomain isomorphism preserves the represented Q-arrow. -/
theorem cospan_eq_of_iso {X Y U V : C}
    (i : X ⟶ U) (p : Y ⟶ U) (j : X ⟶ V) (q : Y ⟶ V)
    [Mono i] [Epi p] [Mono j] [Epi q]
    (e : U ≅ V) (hi : i ≫ e.hom = j) (hp : p ≫ e.hom = q) :
    inflationArrow i ≫ surjectionArrow p = inflationArrow j ≫ surjectionArrow q := by
  have w : pullback.fst i p ≫ j = pullback.snd i p ≫ q := by
    rw [← hi, ← hp, ← Category.assoc, pullback.condition, Category.assoc]
  have w' : pullback.fst j q ≫ i = pullback.snd j q ≫ p := by
    apply (cancel_mono e.hom).1
    simp only [Category.assoc, hi, hp]
    exact pullback.condition
  let a := pullback.lift (pullback.fst i p) (pullback.snd i p) w
  let b := pullback.lift (pullback.fst j q) (pullback.snd j q) w'
  let f : pullback i p ≅ pullback j q :=
    ⟨a, b, by apply pullback.hom_ext <;> simp [a, b],
      by apply pullback.hom_ext <;> simp [a, b]⟩
  rw [← mkHom_cospanSpan, ← mkHom_cospanSpan]
  apply mkHom_eq_of_apexIso _ _ _ _ f
  · simp [f, a, cospanSpan]
  · simp [f, a, cospanSpan]

/-- Complete classification of mono-epi cospan representatives. -/
theorem cospan_eq_iff_iso {X Y U V : C}
    (i : X ⟶ U) (p : Y ⟶ U) (j : X ⟶ V) (q : Y ⟶ V)
    [Mono i] [Epi p] [Mono j] [Epi q] :
    inflationArrow i ≫ surjectionArrow p = inflationArrow j ≫ surjectionArrow q ↔
      ∃ e : U ≅ V, i ≫ e.hom = j ∧ p ≫ e.hom = q := by
  constructor
  · exact exists_cospanIso_of_eq i p j q
  · rintro ⟨e, hi, hp⟩
    exact cospan_eq_of_iso i p j q e hi hp

/-- Every Q-arrow has an ordinary mono-epi cospan representative. -/
theorem exists_cospan {X Y : C}
    (f : of (abelianExactStructure C).deflation (abelianExactStructure C).inflation X ⟶
      of (abelianExactStructure C).deflation (abelianExactStructure C).inflation Y) :
    ∃ (U : C) (i : X ⟶ U) (p : Y ⟶ U) (_ : Mono i) (_ : Epi p),
      inflationArrow i ≫ surjectionArrow p = f := by
  obtain ⟨s, rfl⟩ := Quotient.exists_rep f
  exact ⟨pushout s.l s.r, pushout.inl s.l s.r, pushout.inr s.l s.r,
    inferInstance, inferInstance, span_cospan_factorization s⟩

end Q
end Quillen
