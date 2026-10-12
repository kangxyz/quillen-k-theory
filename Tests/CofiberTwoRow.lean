/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.SConstruction.Rows.CofiberTwoFaces

/-! # Consumers of the literal original cofiber row -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Quillen.Waldhausen Quillen.Waldhausen.QuotientRows
open scoped Simplicial
universe u v
namespace Quillen.Tests.CofiberTwoRow
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  (W : Structure C) {A B Q : C} (i : A ⟶ B) (q : B ⟶ Q) (hiq : i ≫ q = 0)

/-- The actual horizontal arrow remains the given cofibration. -/
theorem original_inclusion :
    HEq ((cofiberTwoDiagram W i q hiq).map (homOfLE
      (show interval (n := ⦋2⦌) 0 1 (by decide) ≤ interval 0 2 (by decide) from
        ⟨le_rfl, by decide⟩))) i := by
  simp [cofiberTwoDiagram, cofiberTwoMap, interval]

/-- The actual quotient arrow remains the given quotient. -/
theorem original_quotient :
    HEq ((cofiberTwoDiagram W i q hiq).map (homOfLE
      (show interval (n := ⦋2⦌) 0 2 (by decide) ≤ interval 1 2 (by decide) from
        ⟨by decide, le_rfl⟩))) q := by
  simp [cofiberTwoDiagram, cofiberTwoMap, interval]

/-- Actual cofibration and pushout data certify the genuine S-row. -/
theorem genuine_row (hi : W.cof i)
    (hQ : IsPushout i (0 : A ⟶ W.zero) q (0 : W.zero ⟶ Q)) :
    IsRow W (cofiberTwoDiagram W i q hiq) := cofiberTwoDiagram_isRow W i q hiq hi hQ

/-- The first short face retains the original source loop row. -/
theorem original_source_face :
    indexMap (SimplexCategory.δ (2 : Fin 3)) ⋙ cofiberTwoDiagram W i q hiq = oneDiagram W A :=
  cofiberTwoDiagram_face W i q hiq 2

/-- The other short face retains the original quotient loop row. -/
theorem original_quotient_face :
    indexMap (SimplexCategory.δ (0 : Fin 3)) ⋙ cofiberTwoDiagram W i q hiq = oneDiagram W Q :=
  cofiberTwoDiagram_face W i q hiq 0

/-- The long face retains the original middle object loop row. -/
theorem original_middle_face :
    indexMap (SimplexCategory.δ (1 : Fin 3)) ⋙ cofiberTwoDiagram W i q hiq = oneDiagram W B :=
  cofiberTwoDiagram_face W i q hiq 1

end Quillen.Tests.CofiberTwoRow
