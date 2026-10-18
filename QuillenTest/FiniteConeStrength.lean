/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.KTheory.Bass.FiniteConeStrength
public import Quillen.Topology.Prespectrum.LoopTranspose

/-! Actual single-strength stability at every normalized Model stage. -/
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open Quillen.KTheory.Bass Quillen.KTheory.Bass.FiniteConeTopology
open Quillen.KTheory.Bass.FiniteConeStrength
open Quillen.LoopPrespectrum.FiniteParameterLooping
universe u v w
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
    (M : C ⥤ Model.{w}) (i : ℕ) (X : C)

example :
    (loopDiagram i (iterate Q i (M ⋙ prespectrumFunctor))).obj X =
      loops i ((iterate Q i (M ⋙ prespectrumFunctor)).obj X) :=
  loopDiagram_obj i _ X

example (d : ℤ) :
    IsIso ((stableHomotopyFunctor d).map (LoopStrength.strength Q
      (loopDiagram i (iterate Q i (M ⋙ prespectrumFunctor))) X)) :=
  model_strength_stable Q i i M X d

#print axioms model_strength_stable
