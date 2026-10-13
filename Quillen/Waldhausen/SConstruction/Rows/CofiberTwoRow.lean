/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Rows.Basic

/-!
# The literal two-step row of a displayed cofiber sequence

The six original interval objects are the chosen zero, source, middle, chosen zero,
quotient and chosen zero. The supplied original cofibration and quotient are its two
nontrivial short maps; their composite is the literal zero map.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe u v
namespace Quillen.Waldhausen.QuotientRows
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  (W : Structure C) {A B Q : C} (i : A ⟶ B) (q : B ⟶ Q)

/-- The six literal objects of the displayed two-step quotient row. -/
abbrev cofiberTwoObject (p : Interval ⦋2⦌) : C :=
  match p.val.1.val, p.val.2.val with
  | 0, 1 => A
  | 0, 2 => B
  | 1, 2 => Q
  | _, _ => W.zero

/-- The actual original cofibration and quotient, with zero maps on the other strict intervals. -/
def cofiberTwoMap {p r : Interval ⦋2⦌} (_f : p ⟶ r) :
    cofiberTwoObject W (A := A) (B := B) (Q := Q) p ⟶
      cofiberTwoObject W (A := A) (B := B) (Q := Q) r := by
  classical
  by_cases h : p = r
  · exact eqToHom (congrArg (cofiberTwoObject W (A := A) (B := B) (Q := Q)) h)
  · by_cases h₁ : p = interval 0 1 (by decide) ∧ r = interval 0 2 (by decide)
    · exact eqToHom (congrArg (cofiberTwoObject W (A := A) (B := B) (Q := Q)) h₁.1) ≫
        i ≫ eqToHom (congrArg (cofiberTwoObject W (A := A) (B := B) (Q := Q)) h₁.2.symm)
    · by_cases h₂ : p = interval 0 2 (by decide) ∧ r = interval 1 2 (by decide)
      · exact eqToHom (congrArg (cofiberTwoObject W (A := A) (B := B) (Q := Q)) h₂.1) ≫
          q ≫ eqToHom (congrArg (cofiberTwoObject W (A := A) (B := B) (Q := Q)) h₂.2.symm)
      · exact 0

private theorem cofiberTwoMap_comp_00
    {p s : Interval ⦋2⦌} (f : p ⟶ interval 0 0 (by decide))
    (g : interval 0 0 (by decide) ⟶ s) :
    cofiberTwoMap W i q (f ≫ g) = cofiberTwoMap W i q f ≫ cofiberTwoMap W i q g := by
  rcases p with ⟨⟨a, b⟩, hab⟩
  rcases s with ⟨⟨c, d⟩, hcd⟩
  change a.val ≤ b.val at hab
  change c.val ≤ d.val at hcd
  have hf : a.val ≤ 0 ∧ b.val ≤ 0 := leOfHom f
  have hg : 0 ≤ c.val ∧ 0 ≤ d.val := leOfHom g
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    dsimp at hab hcd hf hg ⊢ <;>
    solve
    | omega
    | exact W.isZero.eq_of_src _ _

private theorem cofiberTwoMap_comp_01
    {p s : Interval ⦋2⦌} (f : p ⟶ interval 0 1 (by decide))
    (g : interval 0 1 (by decide) ⟶ s) :
    cofiberTwoMap W i q (f ≫ g) = cofiberTwoMap W i q f ≫ cofiberTwoMap W i q g := by
  rcases p with ⟨⟨a, b⟩, hab⟩
  rcases s with ⟨⟨c, d⟩, hcd⟩
  change a.val ≤ b.val at hab
  change c.val ≤ d.val at hcd
  have hf : a.val ≤ 0 ∧ b.val ≤ 1 := leOfHom f
  have hg : 0 ≤ c.val ∧ 1 ≤ d.val := leOfHom g
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    dsimp at hab hcd hf hg ⊢ <;>
    solve
    | omega
    | exact W.isZero.eq_of_src _ _
    | exact W.isZero.eq_of_tgt _ _
    | simp [cofiberTwoMap, interval]

private theorem cofiberTwoMap_comp_02 (hiq : i ≫ q = 0)
    {p s : Interval ⦋2⦌} (f : p ⟶ interval 0 2 (by decide))
    (g : interval 0 2 (by decide) ⟶ s) :
    cofiberTwoMap W i q (f ≫ g) = cofiberTwoMap W i q f ≫ cofiberTwoMap W i q g := by
  rcases p with ⟨⟨a, b⟩, hab⟩
  rcases s with ⟨⟨c, d⟩, hcd⟩
  change a.val ≤ b.val at hab
  change c.val ≤ d.val at hcd
  have hf : a.val ≤ 0 ∧ b.val ≤ 2 := leOfHom f
  have hg : 0 ≤ c.val ∧ 2 ≤ d.val := leOfHom g
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    dsimp at hab hcd hf hg ⊢ <;>
    solve
    | omega
    | exact W.isZero.eq_of_src _ _
    | exact W.isZero.eq_of_tgt _ _
    | simp [cofiberTwoMap, interval, hiq]

private theorem cofiberTwoMap_comp_11
    {p s : Interval ⦋2⦌} (f : p ⟶ interval 1 1 (by decide))
    (g : interval 1 1 (by decide) ⟶ s) :
    cofiberTwoMap W i q (f ≫ g) = cofiberTwoMap W i q f ≫ cofiberTwoMap W i q g := by
  rcases p with ⟨⟨a, b⟩, hab⟩
  rcases s with ⟨⟨c, d⟩, hcd⟩
  change a.val ≤ b.val at hab
  change c.val ≤ d.val at hcd
  have hf : a.val ≤ 1 ∧ b.val ≤ 1 := leOfHom f
  have hg : 1 ≤ c.val ∧ 1 ≤ d.val := leOfHom g
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    dsimp at hab hcd hf hg ⊢ <;>
    solve
    | omega
    | exact W.isZero.eq_of_src _ _
    | exact W.isZero.eq_of_tgt _ _
    | simp [cofiberTwoMap, interval]

private theorem cofiberTwoMap_comp_12
    {p s : Interval ⦋2⦌} (f : p ⟶ interval 1 2 (by decide))
    (g : interval 1 2 (by decide) ⟶ s) :
    cofiberTwoMap W i q (f ≫ g) = cofiberTwoMap W i q f ≫ cofiberTwoMap W i q g := by
  rcases p with ⟨⟨a, b⟩, hab⟩
  rcases s with ⟨⟨c, d⟩, hcd⟩
  change a.val ≤ b.val at hab
  change c.val ≤ d.val at hcd
  have hf : a.val ≤ 1 ∧ b.val ≤ 2 := leOfHom f
  have hg : 1 ≤ c.val ∧ 2 ≤ d.val := leOfHom g
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    dsimp at hab hcd hf hg ⊢ <;>
    solve
    | omega
    | exact W.isZero.eq_of_src _ _
    | exact W.isZero.eq_of_tgt _ _
    | simp [cofiberTwoMap, interval]

private theorem cofiberTwoMap_comp_22
    {p s : Interval ⦋2⦌} (f : p ⟶ interval 2 2 (by decide))
    (g : interval 2 2 (by decide) ⟶ s) :
    cofiberTwoMap W i q (f ≫ g) = cofiberTwoMap W i q f ≫ cofiberTwoMap W i q g := by
  rcases p with ⟨⟨a, b⟩, hab⟩
  rcases s with ⟨⟨c, d⟩, hcd⟩
  change a.val ≤ b.val at hab
  change c.val ≤ d.val at hcd
  have hf : a.val ≤ 2 ∧ b.val ≤ 2 := leOfHom f
  have hg : 2 ≤ c.val ∧ 2 ≤ d.val := leOfHom g
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    dsimp at hab hcd hf hg ⊢ <;>
    solve
    | omega
    | exact W.isZero.eq_of_src _ _
    | exact W.isZero.eq_of_tgt _ _

/-- The literal maps form a functor exactly when the displayed composite is zero. -/
def cofiberTwoDiagram (hiq : i ≫ q = 0) : Interval ⦋2⦌ ⥤ C where
  obj := cofiberTwoObject W (A := A) (B := B) (Q := Q)
  map := cofiberTwoMap W i q
  map_id p := by simp [cofiberTwoMap]
  map_comp {p r s} f g := by
    rcases r with ⟨⟨a, b⟩, hab⟩
    change a.val ≤ b.val at hab
    fin_cases a <;> fin_cases b <;> dsimp at hab ⊢ <;> first
    | omega
    | exact cofiberTwoMap_comp_00 W i q f g
    | exact cofiberTwoMap_comp_01 W i q f g
    | exact cofiberTwoMap_comp_02 W i q hiq f g
    | exact cofiberTwoMap_comp_11 W i q f g
    | exact cofiberTwoMap_comp_12 W i q f g
    | exact cofiberTwoMap_comp_22 W i q f g

/-- The displayed original cofiber square supplies every actual two-row axiom. -/
theorem cofiberTwoDiagram_isRow (hiq : i ≫ q = 0) (hi : W.cof i)
    (hQ : IsPushout i (0 : A ⟶ W.zero) q (0 : W.zero ⟶ Q)) :
    IsRow W (cofiberTwoDiagram W i q hiq) where
  zero k := by
    fin_cases k <;> exact W.isZero
  cofibration a b c hab hbc := by
    have hz (X : C) : W.cof (0 : W.zero ⟶ X) := by
      convert W.cof_zero X using 1
      exact W.isZero.eq_of_src _ _
    change a.val ≤ b.val at hab
    change b.val ≤ c.val at hbc
    fin_cases a <;> fin_cases b <;> fin_cases c <;>
      dsimp at hab hbc ⊢ <;>
      solve
      | omega
      | exact W.cof.id_mem _
      | exact hz _
      | simpa [cofiberTwoDiagram, cofiberTwoMap, interval] using hi
  quotient a b c hab hbc := by
    change a.val ≤ b.val at hab
    change b.val ≤ c.val at hbc
    fin_cases a <;> fin_cases b <;> fin_cases c <;>
      dsimp at hab hbc ⊢ <;>
      solve
      | omega
      | exact IsPushout.id_horiz _
      | exact IsPushout.of_id_snd
      | simpa [cofiberTwoDiagram, cofiberTwoMap, interval] using hQ

/-- The original quotient square itself gives the required zero composite. -/
theorem cofiberTwo_comp_eq_zero
    (hQ : IsPushout i (0 : A ⟶ W.zero) q (0 : W.zero ⟶ Q)) : i ≫ q = 0 := by
  simpa only [zero_comp] using hQ.w

/-- The actual displayed quotient sequence as an object of the original S-row category. -/
def cofiberTwoRow (hi : W.cof i)
    (hQ : IsPushout i (0 : A ⟶ W.zero) q (0 : W.zero ⟶ Q)) : Obj W ⦋2⦌ :=
  ⟨cofiberTwoDiagram W i q (cofiberTwo_comp_eq_zero W i q hQ),
    cofiberTwoDiagram_isRow W i q (cofiberTwo_comp_eq_zero W i q hQ) hi hQ⟩

end Quillen.Waldhausen.QuotientRows
