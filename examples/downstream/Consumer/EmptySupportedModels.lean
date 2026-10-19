/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalEmptySupportedModels

/-! # Original empty-support forgetting after an incoming finite-stage map -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS
open Quillen.PerfectComplexes.GlobalSectionChangeIndex
universe u
namespace Consumer.EmptySupportedModels

/-- Restoring empty support then applying the original forget map retains every incoming map. -/
theorem bottomForget_after_inverse (X : Scheme.{u}) (n : ℕ)
    {A : SSet.{u + 1}} (g : A ⟶ (stages n).obj (globalModel.obj (op X))) :
    g ≫ (stages n).map (bottomSupportedModelIso (op X)).inv ≫
      (stages n).map (supportedForget (X := op X) (⊥ : X.Opens).ι) = g := by
  change g ≫ ((stages n).mapIso (bottomSupportedModelIso (op X))).inv ≫
    ((stages n).mapIso (bottomSupportedModelIso (op X))).hom = g
  rw [Iso.inv_hom_id, Category.comp_id]

end Consumer.EmptySupportedModels
