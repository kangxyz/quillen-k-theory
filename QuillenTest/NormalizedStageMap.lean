/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.KTheory.Bass.NormalizedStageMap
public import Quillen.Topology.Prespectrum.LoopTranspose

/-! Fixed-order loop strength, actual coefficient naturality, and normalized Model stage maps. -/
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open Quillen.KTheory.Bass Quillen.KTheory.Bass.FiniteConeTopology
open Quillen.KTheory.Bass.FiniteConeStrength
open Quillen.KTheory.Bass.IteratedLoopStrength
open Quillen.KTheory.Bass.NormalizedStageMap
open Quillen.LoopPrespectrum.FiniteParameterLooping
universe u v w
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))

example (F : C ⥤ Quillen.LoopPrespectrum.{w}) (j : ℕ) :
    iteratedStrength Q (j + 1) F = strengthDiagram Q (loopDiagram j F) ≫
      Functor.whiskerRight (iteratedStrength Q j F) parameterLoopingFunctor := rfl

example (F : C ⥤ Quillen.LoopPrespectrum.{w}) : stageMap Q 0 F = 𝟙 F := rfl

example (F : C ⥤ Quillen.LoopPrespectrum.{w}) (i : ℕ) :
    stageMap Q (i + 1) F = eqToHom (bass_succ_eq Q i F) ≫
      (strictDiagramFunctor Q).map (stageMap Q i F) ≫
      iteratedStrength Q i (iterate Q i F) ≫ eqToHom (normalized_succ_eq Q i F) := rfl

example (F : C ⥤ Quillen.LoopPrespectrum.{w}) (i : ℕ) {X Y : C} (f : X ⟶ Y) :
    ((strictDiagramIterate Q i).obj F).map f ≫ (stageMap Q i F).app Y =
      (stageMap Q i F).app X ≫ (normalized Q i F).map f :=
  (stageMap Q i F).naturality f

example (M : C ⥤ Model.{w}) (i : ℕ) (X : C) (d : ℤ) :
    IsIso ((stableHomotopyFunctor d).map ((stageMap Q i (M ⋙ prespectrumFunctor)).app X)) :=
  model_stageMap_stable Q i M X d

#print axioms iterated_model_stable
#print axioms model_stageMap_stable
