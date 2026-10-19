/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.FiniteConeCounit
public import Quillen.Topology.Prespectrum.SuspensionLoopUnit

/-!
# Actual stable suspension units at finite loop-cone stages

Every parameter-looped finite cone stage of an original Model diagram has a stable canonical
suspension-loop unit. This uses the literal unit-counit triangle and the proved finite counit,
with no new point-topology, growth, action or telescope hypotheses.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum
open Quillen.LoopPrespectrum.FiniteParameterLooping
open Quillen.Waldhausen.IteratedS
universe u v w
namespace Quillen.KTheory.Bass.FiniteConeTopology
variable {C : Type u} [Category.{v} C]

/-- The original forward unit is stable on each parameter-looped finite Model cone stage. -/
theorem modelLoopsIterate_suspensionLoopUnit_isStableEquivalence
    (Q : C ⥤ Arrow (Arrow C)) (i j : ℕ) (F : C ⥤ Model.{w}) (X : C) :
    IsStableEquivalence (suspensionLoopUnit
      (parameterLooping (loops j ((iterate Q i (F ⋙ prespectrumFunctor)).obj X)))) :=
  suspensionLoopUnit_parameterLooping_isStableEquivalence _
    (modelLoopsIterate_suspensionLoopCounit_isStableEquivalence Q i j F X)

end Quillen.KTheory.Bass.FiniteConeTopology
