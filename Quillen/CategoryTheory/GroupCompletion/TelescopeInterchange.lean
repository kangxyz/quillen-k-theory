/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.CategoryTheory.GroupCompletion.TelescopeTransitionLaws
public import Quillen.CategoryTheory.GroupCompletion.TelescopeIndex

/-! # The original localization–telescope interchange functor

This functor uses the genuine localized stage cocone. Its construction alone
asserts neither full faithfulness nor a topological group-completion theorem.
-/

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
attribute [local instance] monoidalLeftAction

/-- The actual completed telescope maps to localization of the original telescope. -/
def localizationInterchange :
    Grothendieck (localizationDiagram e) ⥤ Localization C (Model e) where
  obj X := (localizationStage e X.base).obj X.fiber
  map {X Y} f := (localizationStageTransition e f.base).app X.fiber ≫
    (localizationStage e Y.base).map f.fiber
  map_id X := by simp [localizationStageTransition_id, eqToHom_map]
  map_comp f g := by simp [localizationStageTransition_comp, eqToHom_map]

/-- The interchange retains the specified stage and both original coordinates. -/
theorem localizationInterchange_obj (X : Grothendieck (localizationDiagram e)) :
    (localizationInterchange e).obj X =
      ⟨X.fiber.obj.1, (stageInclusion e X.base).obj X.fiber.obj.2⟩ := rfl

/-- Restriction to any original completed stage is exactly the localized stage map. -/
theorem localizationInterchange_stage (n : ℕ) :
    Grothendieck.ι (localizationDiagram e) n ⋙ localizationInterchange e =
      localizationStage e n := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro X Y f
  simp [localizationInterchange, Grothendieck.ι, localizationStageTransition_id,
    eqToHom_map]

/-- The original unit entry is retained at every stage, including stage zero. -/
theorem localizationInterchange_stage_unit (n : ℕ) :
    Localization.unitEntry (C := C) (D := C) ⋙
        Grothendieck.ι (localizationDiagram e) n ⋙ localizationInterchange e =
      stageInclusion e n ⋙ Localization.unitEntry (C := C) (D := Model e) := by
  rw [localizationInterchange_stage, localizationStage_unitEntry]

end Quillen.TranslationTelescope
