/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.SConstruction.Rows.CofiberTwoFaces

/-! # The actual weak row comparison for a cofiber prism

The original gluing axiom makes the quotient of a weak cofibration acyclic. This is the
specified zero-to-quotient component required by the actual row comparison.
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

/-- Gluing the actual weak cofibration against its identity square proves the original
zero-to-quotient map weak, without an additional acyclicity hypothesis. -/
theorem cofiberTwo_quotient_weak (hi : W.cof i) (hwi : W.weq i)
    (hQ : IsPushout i (0 : A ⟶ W.zero) q (0 : W.zero ⟶ Q)) :
    W.weq (0 : W.zero ⟶ Q) := by
  apply W.gluing (𝟙 A) i (𝟙 W.zero) (0 : W.zero ⟶ Q)
    (W.cof.id_mem A) hi (IsPushout.id_horiz (0 : A ⟶ W.zero)) hQ
  · simp
  · simp
  · simpa only [zero_comp] using (cofiberTwo_comp_eq_zero W i q hQ).symm
  · simp
  · exact W.weq.id_mem A
  · exact hwi
  · exact W.weq.id_mem W.zero

omit [HasZeroMorphisms C] in
/-- Away from the middle and quotient positions, the two original rows have the same object. -/
theorem cofiberTwoComparison_object_eq (p : Interval ⦋2⦌)
    (h02 : p ≠ interval 0 2 (by decide)) (h12 : p ≠ interval 1 2 (by decide)) :
    cofiberTwoObject W (A := A) (B := A) (Q := W.zero) p =
      cofiberTwoObject W (A := A) (B := B) (Q := Q) p := by
  rcases p with ⟨⟨a, b⟩, hab⟩
  change a.val ≤ b.val at hab
  fin_cases a <;> fin_cases b <;> dsimp at hab ⊢ <;>
    solve
    | omega
    | rfl
    | exact False.elim (h02 rfl)
    | exact False.elim (h12 rfl)

/-- The original row components are identity on the source, the given arrow on the middle,
and zero-to-quotient on the quotient interval. -/
def cofiberTwoComparisonComponent (p : Interval ⦋2⦌) :
    cofiberTwoObject W (A := A) (B := A) (Q := W.zero) p ⟶
      cofiberTwoObject W (A := A) (B := B) (Q := Q) p := by
  classical
  by_cases h02 : p = interval 0 2 (by decide)
  · exact eqToHom (congrArg (cofiberTwoObject W (A := A) (B := A) (Q := W.zero)) h02) ≫
      i ≫ eqToHom (congrArg (cofiberTwoObject W (A := A) (B := B) (Q := Q)) h02.symm)
  · by_cases h12 : p = interval 1 2 (by decide)
    · exact 0
    · exact eqToHom (cofiberTwoComparison_object_eq W p h02 h12)

/-- The original three components give a natural transformation of the entire two-row diagrams.
-/
def cofiberTwoComparison (hiq : i ≫ q = 0) :
    cofiberTwoDiagram W (𝟙 A) (0 : A ⟶ W.zero) (by simp) ⟶
      cofiberTwoDiagram W i q hiq where
  app := cofiberTwoComparisonComponent W i
  naturality p r f := by
    rcases p with ⟨⟨a, b⟩, hab⟩
    rcases r with ⟨⟨c, d⟩, hcd⟩
    change a.val ≤ b.val at hab
    change c.val ≤ d.val at hcd
    have hf : a.val ≤ c.val ∧ b.val ≤ d.val := leOfHom f
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      dsimp at hab hcd hf ⊢ <;>
      solve
      | omega
      | exact W.isZero.eq_of_src _ _
      | exact W.isZero.eq_of_tgt _ _
      | simp only [cofiberTwoDiagram, Fin.isValue, cofiberTwoMap, ↓reduceDIte,
          eqToHom_refl, cofiberTwoComparisonComponent, interval, Nat.reduceAdd,
          Subtype.mk.injEq, Prod.mk.injEq, Fin.reduceEq, and_false, zero_ne_one,
          and_self, Category.comp_id, Category.id_comp, one_ne_zero, and_true,
          comp_zero, hiq] <;> exact Category.id_comp i

/-- The identity row has its literal chosen-zero quotient, supplied by the actual identity square.
-/
theorem cofiberTwo_identity_square :
    IsPushout (𝟙 A) (0 : A ⟶ W.zero) (0 : A ⟶ W.zero) (0 : W.zero ⟶ W.zero) := by
  convert IsPushout.id_horiz (0 : A ⟶ W.zero) using 1
  exact W.isZero.eq_of_src _ _

/-- The original row transformation is a morphism between the two genuine quotient rows. -/
def cofiberTwoRowComparison (hi : W.cof i)
    (hQ : IsPushout i (0 : A ⟶ W.zero) q (0 : W.zero ⟶ Q)) :
    cofiberTwoRow W (𝟙 A) (0 : A ⟶ W.zero) (W.cof.id_mem A)
        (cofiberTwo_identity_square W) ⟶ cofiberTwoRow W i q hi hQ :=
  (objects W ⦋2⦌).homMk (cofiberTwoComparison W i q (cofiberTwo_comp_eq_zero W i q hQ))

/-- Every component of the actual row comparison is weak; the zero-to-quotient component
uses the proved original gluing square. -/
theorem cofiberTwoRowComparison_weak (hi : W.cof i) (hwi : W.weq i)
    (hQ : IsPushout i (0 : A ⟶ W.zero) q (0 : W.zero ⟶ Q)) :
    weq W ⦋2⦌ (cofiberTwoRowComparison W i q hi hQ) := by
  rintro ⟨⟨a, b⟩, hab⟩
  change a.val ≤ b.val at hab
  change W.weq (cofiberTwoComparisonComponent W i ⟨(a, b), _⟩)
  fin_cases a <;> fin_cases b <;> dsimp at hab ⊢ <;>
    solve
    | omega
    | simp only [cofiberTwoComparisonComponent, interval, Nat.reduceAdd,
        Subtype.mk.injEq, Prod.mk.injEq, Fin.reduceEq, and_false, and_true, and_self,
        zero_ne_one, one_ne_zero, ↓reduceDIte, eqToHom_refl, Category.comp_id,
        Category.id_comp]
      first
      | exact W.weq.id_mem _
      | exact hwi
      | exact cofiberTwo_quotient_weak W i q hi hwi hQ

/-- The source component is the original identity, with its actual endpoint types retained. -/
theorem cofiberTwoRowComparison_source (hi : W.cof i)
    (hQ : IsPushout i (0 : A ⟶ W.zero) q (0 : W.zero ⟶ Q)) :
    HEq ((cofiberTwoRowComparison W i q hi hQ).hom.app
      (interval (n := ⦋2⦌) 0 1 (by decide))) (𝟙 A) := by
  simp only [Fin.isValue, interval, Nat.reduceAdd, cofiberTwoRowComparison, cofiberTwoComparison,
    ObjectProperty.homMk_hom, cofiberTwoComparisonComponent, Subtype.mk.injEq, Prod.mk.injEq,
    Fin.reduceEq, and_false, ↓reduceDIte, zero_ne_one, and_self, eqToHom_refl, heq_eq_eq]
  rfl

/-- The middle component is exactly the given original weak cofibration. -/
theorem cofiberTwoRowComparison_middle (hi : W.cof i)
    (hQ : IsPushout i (0 : A ⟶ W.zero) q (0 : W.zero ⟶ Q)) :
    HEq ((cofiberTwoRowComparison W i q hi hQ).hom.app
      (interval (n := ⦋2⦌) 0 2 (by decide))) i := by
  simp [cofiberTwoRowComparison, cofiberTwoComparison, cofiberTwoComparisonComponent, interval]

/-- The quotient component is the literal original zero-to-quotient arrow. -/
theorem cofiberTwoRowComparison_quotient (hi : W.cof i)
    (hQ : IsPushout i (0 : A ⟶ W.zero) q (0 : W.zero ⟶ Q)) :
    HEq ((cofiberTwoRowComparison W i q hi hQ).hom.app
      (interval (n := ⦋2⦌) 1 2 (by decide))) (0 : W.zero ⟶ Q) := by
  simp [cofiberTwoRowComparison, cofiberTwoComparison, cofiberTwoComparisonComponent, interval]

end Quillen.Waldhausen.QuotientRows
