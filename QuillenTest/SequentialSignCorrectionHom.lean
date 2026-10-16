/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Limits.Shapes.SequentialSystem.SignCorrection

/-! # Exact component and successor consumers for sign-corrected stage maps -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory
universe u v
namespace QuillenTest.SequentialSignCorrectionHom
variable {C : Type u} [Category.{v} C] [Preadditive C] {F G : ℕ ⥤ C}
variable (a : ∀ n, F.obj n ⟶ G.obj n)
variable (h : ∀ n, F.map (homOfLE (Nat.le_succ n)) ≫ a (n + 1) =
  -(a n ≫ G.map (homOfLE (Nat.le_succ n))))

/-- The first stage is the unchanged original map. -/
theorem original_stage_zero :
    (CategoryTheory.Limits.SequentialSystem.signCorrectionHom a h).app 0 = a 0 := by
  simp

/-- The next stage is exactly the negative original map. -/
theorem original_stage_one :
    (CategoryTheory.Limits.SequentialSystem.signCorrectionHom a h).app 1 = -a 1 := by
  simp

/-- The actual successor arrows commute after the explicit correction. -/
theorem original_successor_square (n : ℕ) :
    F.map (homOfLE (Nat.le_succ n)) ≫
        (CategoryTheory.Limits.SequentialSystem.signCorrectionHom a h).app (n + 1) =
      (CategoryTheory.Limits.SequentialSystem.signCorrectionHom a h).app n ≫
        G.map (homOfLE (Nat.le_succ n)) :=
  (CategoryTheory.Limits.SequentialSystem.signCorrectionHom a h).naturality _

end QuillenTest.SequentialSignCorrectionHom
