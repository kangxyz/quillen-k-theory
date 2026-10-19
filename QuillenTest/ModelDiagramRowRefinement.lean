/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.ModelDiagramRowRefinementNaturality

/-! Whole index arrows retain the two actual row parameters at every finite Bass stage. -/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open Quillen.KTheory.Bass.ModelDiagramRowRefinement
open scoped Topology unitInterval
universe u v w
namespace QuillenTest.ModelDiagramRowRefinement
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  (i : ℕ) (F : C ⥤ Model.{w}) {X Y : C} (f : X ⟶ Y)

/-- At positive levels the genuine coefficient arrow keeps the whole row parameter unchanged. -/
theorem map_succ (k : ℕ)
    (γ : Path ((source Q i F X).point (k + 2)) ((source Q i F X).point (k + 2)))
    (r : unitInterval) :
    Path.toContinuousMap (((diagram Q i F).map f).map (k + 1) γ) r =
      ((sourceDiagram Q i F).map f).map (k + 2) (γ r) := rfl

/-- Both row parameters survive the actual degree-zero coefficient arrow. -/
theorem map_zero
    (γ : Path (Path.refl ((source Q i F X).point 2))
      (Path.refl ((source Q i F X).point 2))) (r s : unitInterval) :
    Path.toContinuousMap (Path.toContinuousMap (((diagram Q i F).map f).map 0 γ) r) s =
      ((sourceDiagram Q i F).map f).map 2 (γ r s) := rfl

/-- The natural comparison uses the actual original source arrow before the whole refinement. -/
theorem comparison_zero_square (x : (source Q i F X).space 0) (r s : unitInterval) :
    Path.toContinuousMap (Path.toContinuousMap
      ((comparison Q i F Y).map 0 (((sourceDiagram Q i F).map f).map 0 x)) r) s =
    Path.toContinuousMap (Path.toContinuousMap
      (((diagram Q i F).map f).map 0 ((comparison Q i F X).map 0 x)) r) s := by
  have h := comparison_naturality Q i F f
  exact congrArg (fun a : source Q i F X ⟶ carrier Q i F Y =>
    Path.toContinuousMap (Path.toContinuousMap (a.map 0 x) r) s) h

end QuillenTest.ModelDiagramRowRefinement
