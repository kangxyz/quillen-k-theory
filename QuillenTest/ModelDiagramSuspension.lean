/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.ModelDiagramSuspension

/-!
# Original Bass-iterate suspension regression

The second-stage unit is tested on the literal nested Bass functor, including its intervening
parameter loop. The sequential pushout's doubled offset is checked at every original point.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open Quillen.KTheory.Bass
open Quillen.KTheory.Bass.ModelDiagramSuspension
universe u v w
namespace QuillenTest.ModelDiagramSuspension
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  (F : C ⥤ Model.{w}) (X : C)

/-- This is the literal second Bass stage, with its intervening loop retained. -/
theorem second_current_unit :
    IsStableEquivalence (suspensionLoopUnit
      (((strictDiagramFunctor Q).obj
        ((strictDiagramFunctor Q).obj (F ⋙ prespectrumFunctor))).obj X)) :=
  unit_stable Q 1 F X

/-- The offset used for the next suspension column is valid at every displayed point. -/
theorem sequential_offset (i n k : ℕ) (hk : k < n + 2)
    (x : (parameterLooping (suspensionCone
      (((strictDiagramIterate Q (i + 1)).obj (F ⋙ prespectrumFunctor)).obj X))).space
        (n + 2 * (i + 1) + 2)) :
    Subsingleton (HomotopyGroup.Pi k ((parameterLooping (suspensionCone
      (((strictDiagramIterate Q (i + 1)).obj (F ⋙ prespectrumFunctor)).obj X))).space
        (n + 2 * (i + 1) + 2)) x) :=
  homotopyGroup_subsingleton_at_offset Q (i + 1) F X
    (2 * (i + 1)) (by omega) n k hk x

end QuillenTest.ModelDiagramSuspension
