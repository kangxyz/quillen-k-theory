/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.ModelDiagramStabilizedTarget

/-!
# Current-stage stabilized target regression

The original two independent loop times remain in their specified order after the unit and
refinement. The original second Bass stage and the doubled sequential growth offset are
checked on literal objects rather than on stably equivalent replacements.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open Quillen.KTheory.Bass Quillen.KTheory.Bass.ModelDiagramStabilizedTarget
universe u v w
namespace QuillenTest.ModelDiagramStabilizedTarget
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  (F : C ⥤ Model.{w}) (X : C)

/-- Neither loop time is silently interchanged with the original structure time. -/
theorem unit_refinement_two_times (i n : ℕ)
    (γ : (parameterLooping (cone Q i F X)).space n) (r s : unitInterval) :
    Path.toContinuousMap (Path.toContinuousMap
        ((suspensionLoopUnit (parameterLooping (cone Q i F X)) ≫
          refinement Q i F X).map n γ) r) s =
      (cone Q i F X).structureMap n (Path.toContinuousMap γ r) s := by
  rw [unit_refinement]
  rfl

/-- The refinement has the literal second Bass stage as its looped-suspension source. -/
theorem second_current_refinement :
    IsStableEquivalence (currentRefinement Q 1 F X) :=
  currentRefinement_stable Q 1 F X

/-- The actual target satisfies the sequential pushout's doubled offset at every point. -/
theorem sequential_offset (i n k : ℕ) (hk : k < n + 2)
    (x : (target Q i F X).space (n + 2 * (i + 1) + 2)) :
    Subsingleton (HomotopyGroup.Pi k
      ((target Q i F X).space (n + 2 * (i + 1) + 2)) x) :=
  homotopyGroup_subsingleton_at_offset Q i F X (2 * (i + 1)) (by omega) n k hk x

end QuillenTest.ModelDiagramStabilizedTarget
