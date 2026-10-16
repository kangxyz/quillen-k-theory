/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.CategoryTheory.Bicategory.IsoQuotient
public import Mathlib.CategoryTheory.Bicategory.Span.Basic

/-!
# The Q-style restricted-span category

This file constructs the category of admissible spans from the precise
pullback-calculus hypotheses. It does not assert that arbitrary morphism
properties form an exact structure. The proved adapter from exact categories
is provided separately by `CategoryTheory.ExactCategory.ExactStructure` and `Quillen.KTheory`.

The left leg is the deflation (admissible epimorphism); the right leg is the
inflation (admissible monomorphism). Composition uses the actual categorical
pullback supplied by mathlib's restricted-span bicategory. Only the mixed
pullbacks are required, rather than all pullbacks in the category.
-/
@[expose] public section


noncomputable section

universe v u

open CategoryTheory

namespace Quillen

variable {C : Type u} [Category.{v} C]
  (deflation inflation : MorphismProperty C)
  [deflation.ContainsIdentities] [inflation.ContainsIdentities]
  [deflation.IsStableUnderComposition] [inflation.IsStableUnderComposition]
  [deflation.HasPullbacksAgainst inflation]
  [deflation.IsStableUnderBaseChangeAgainst inflation]
  [inflation.IsStableUnderBaseChangeAgainst deflation]

/-- The category of restricted spans modulo apex isomorphism. Once the
properties are obtained from an exact structure, this is its Q-construction. -/
abbrev Q := IsoQuotient (Span.SpanBicat C deflation inflation)

namespace Q

/-- An original object, viewed as an object of the restricted-span category. -/
def of (X : C) : Q deflation inflation := ⟨⟨X⟩⟩

/-- An admissible span determines a Q-morphism. -/
def mkHom {X Y : C} (s : Span deflation inflation X Y) :
    of deflation inflation X ⟶ of deflation inflation Y :=
  IsoQuotient.mkHom s

/-- Two span representatives determine the same arrow precisely when they
are isomorphic as spans. -/
theorem mkHom_eq_iff {X Y : C} (s t : Span deflation inflation X Y) :
    mkHom deflation inflation s = mkHom deflation inflation t ↔ Nonempty (s ≅ t) :=
  Quotient.eq

/-- Apex isomorphisms commuting with both legs yield equal Q-morphisms. -/
theorem mkHom_eq_of_apexIso {X Y : C} (s t : Span deflation inflation X Y)
    (e : s.apex ≅ t.apex) (hl : e.hom ≫ t.l = s.l) (hr : e.hom ≫ t.r = s.r) :
    mkHom deflation inflation s = mkHom deflation inflation t :=
  IsoQuotient.mkHom_eq_of_iso (Span.mkIso e hl hr)

/-- Identity arrows are represented by identity spans. -/
@[simp]
theorem mkHom_id (X : C) :
    mkHom deflation inflation (Span.id X) = 𝟙 (of deflation inflation X) := rfl

/-- Composition is represented by the genuine pullback composite. -/
@[simp]
theorem mkHom_comp {X Y Z : C} (s : Span deflation inflation X Y)
    (t : Span deflation inflation Y Z) :
    mkHom deflation inflation (Span.comp s t) =
      mkHom deflation inflation s ≫ mkHom deflation inflation t := rfl

omit [deflation.ContainsIdentities] [inflation.ContainsIdentities] in
/-- The representative used by composition has the expected pullback apex. -/
theorem comp_apex {X Y Z : C} (s : Span deflation inflation X Y)
    (t : Span deflation inflation Y Z) :
    (Span.comp s t).apex = Limits.pullback s.r t.l := rfl

/-- No further quotient relation is imposed: equality is precisely a
commuting isomorphism between apices. -/
theorem mkHom_eq_iff_apexIso {X Y : C} (s t : Span deflation inflation X Y) :
    mkHom deflation inflation s = mkHom deflation inflation t ↔
      ∃ e : s.apex ≅ t.apex, e.hom ≫ t.l = s.l ∧ e.hom ≫ t.r = s.r := by
  rw [mkHom_eq_iff]
  constructor
  · rintro ⟨e⟩
    exact ⟨{ hom := e.hom.hom, inv := e.inv.hom,
             hom_inv_id := congrArg Span.Hom.hom e.hom_inv_id,
             inv_hom_id := congrArg Span.Hom.hom e.inv_hom_id },
      e.hom.hom_l, e.hom.hom_r⟩
  · rintro ⟨e, hl, hr⟩
    exact ⟨Span.mkIso e hl hr⟩

end Q
end Quillen
