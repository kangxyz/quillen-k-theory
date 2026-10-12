/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.SConstruction.Rows.CofiberTwoRow
public import Quillen.Waldhausen.SConstruction.Rows.OneRow

/-! # The literal three faces of a displayed cofiber row

The original source, quotient and middle objects occur in the actual three ordinal faces.
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
  (W : Structure C) {A B Q : C} (i : A ⟶ B) (q : B ⟶ Q) (hiq : i ≫ q = 0)

/-- The face order is quotient, middle, source. -/
abbrev cofiberFaceObject (k : Fin 3) : C := match k.val with
  | 0 => Q
  | 1 => B
  | _ => A

/-- Every original face diagram is the literal original one-step row. -/
theorem cofiberTwoDiagram_face (k : Fin 3) :
    indexMap (SimplexCategory.δ k) ⋙ cofiberTwoDiagram W i q hiq =
      oneDiagram W (cofiberFaceObject (A := A) (B := B) (Q := Q) k) := by
  have hobj : ∀ p, (indexMap (SimplexCategory.δ k) ⋙ cofiberTwoDiagram W i q hiq).obj p =
      (oneDiagram W (cofiberFaceObject (A := A) (B := B) (Q := Q) k)).obj p := by
    rintro ⟨⟨a,b⟩, hab⟩
    change a.val ≤ b.val at hab
    fin_cases a <;> fin_cases b <;> fin_cases k <;> dsimp at hab ⊢ <;> solve | omega | rfl
  refine CategoryTheory.Functor.ext hobj ?_
  rintro ⟨⟨a,b⟩, hab⟩ ⟨⟨c,d⟩, hcd⟩ f
  change a.val ≤ b.val at hab
  change c.val ≤ d.val at hcd
  have hf : a.val ≤ c.val ∧ b.val ≤ d.val := leOfHom f
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> fin_cases k <;>
    dsimp at hab hcd hf ⊢ <;>
    solve
    | omega
    | exact W.isZero.eq_of_src _ _
    | exact W.isZero.eq_of_tgt _ _
    | have he : f = 𝟙 _ := Subsingleton.elim _ _
      subst f
      simp

end Quillen.Waldhausen.QuotientRows
