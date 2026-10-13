/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.CategoryTheory.GroupCompletion.TelescopeStages
public import Quillen.CategoryTheory.GroupCompletion.TelescopeDiagram
public import Quillen.CategoryTheory.GroupCompletion.ActedFunctorNaturality
public import Quillen.CategoryTheory.Monoidal.TranslationTelescopeTransitions

/-! # Actual completed-stage transitions into localization of the telescope -/

@[expose] public section
noncomputable section
open CategoryTheory MonoidalCategory
universe u v
namespace Quillen.TranslationTelescope
open GroupCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (e : C)
attribute [local instance] monoidalLeftAction

/-- Localize the actual linear stage transition, retaining all iterated lineators. -/
def localizationStageTransition {n m : ℕ} (h : n ⟶ m) :
    localizationStage e n ⟶
      (localizationDiagram e |>.map h).toFunctor ⋙ localizationStage e m := by
  letI := rightIterateLinear e (m - n)
  letI := stageTransitionTargetLinear e n m
  let η := Localization.actedMapNatTrans (C := C) (stageInclusion e n)
    (EndofunctorTelescope.iterate (tensorRight e) (m - n) ⋙ stageInclusion e m)
    (stageTransition e h) (by
      intro P X
      change 𝟙 _ ≫ (stageTransition e h).app (P ⊗ X) =
        (leftTranslation e P).map ((stageTransition e h).app X) ≫
          (𝟙 _ ≫ stageArrow e m (rightIterateLineator e (m - n) P X))
      erw [Category.id_comp, Category.id_comp]
      exact stageTransition_action e h P X)
  exact η ≫ eqToHom
    (Localization.actedMapFunctor_composition (C := C)
      (EndofunctorTelescope.iterate (tensorRight e) (m - n)) (stageInclusion e m))

/-- A transition component is precisely the original telescope arrow with unit denominator. -/
theorem localizationStageTransition_app {n m : ℕ} (h : n ⟶ m) (X : Localization C C) :
    (localizationStageTransition e h).app X =
      ActionLocalization.ofHom (C := C)
        (X := (X.obj.1, (stageInclusion e n).obj X.obj.2))
        (Y := (X.obj.1, (stageInclusion e m).obj
          ((EndofunctorTelescope.iterate (tensorRight e) (m - n)).obj X.obj.2)))
        (𝟙 X.obj.1, (stageTransition e h).app X.obj.2) := by
  simp [localizationStageTransition, Localization.actedMapNatTrans_app, eqToHom_app]

end Quillen.TranslationTelescope
