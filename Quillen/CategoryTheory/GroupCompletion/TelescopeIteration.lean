/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.CategoryTheory.GroupCompletion.ActedFunctorComposition
public import Quillen.CategoryTheory.GroupCompletion.Translation
public import Quillen.Aglib.CategoryTheory.Monoidal.Action.RightTensorLinear

/-! # Actual completed iterates and their original associator lineators -/

@[expose] public section

open Quillen.GroupCompletion

open CategoryTheory MonoidalCategory
universe u v
namespace Quillen.TranslationTelescope
open GroupCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (e : C)

/-- Localization of the specified actual right-translation iterate. -/
def localizationIteration (n : ℕ) : Localization C C ⥤ Localization C C :=
  letI := rightIterateLinear e n
  Localization.actedMapFunctor (EndofunctorTelescope.iterate (tensorRight e) n)

/-- Its objects retain the original first coordinate and actual second-coordinate iterate. -/
theorem localizationIteration_obj (n : ℕ) (X : Localization C C) :
    (localizationIteration e n).obj X =
      ⟨X.obj.1, (EndofunctorTelescope.iterate (tensorRight e) n).obj X.obj.2⟩ := rfl

/-- Zero iteration is the actual identity on the completed category. -/
theorem localizationIteration_zero : localizationIteration e 0 = 𝟭 (Localization C C) :=
  Localization.actedMapFunctor_identity

/-- Each successor is exactly the original completed right translation. -/
theorem localizationIteration_succ (n : ℕ) :
    localizationIteration e (n + 1) =
      localizationIteration e n ⋙ Localization.secondTranslation e := by
  let := rightIterateLinear e n
  let := rightTensorLinear e
  exact Localization.actedMapFunctor_composition (EndofunctorTelescope.iterate (tensorRight e) n)
    (tensorRight e)

/-- The explicit-lineator model agrees with the original endofunctor iterate. -/
theorem localizationIteration_eq (n : ℕ) :
    localizationIteration e n =
      EndofunctorTelescope.iterate (Localization.secondTranslation e) n := by
  induction n with
  | zero => exact localizationIteration_zero e
  | succ n ih => rw [localizationIteration_succ, ih]; rfl

end Quillen.TranslationTelescope
