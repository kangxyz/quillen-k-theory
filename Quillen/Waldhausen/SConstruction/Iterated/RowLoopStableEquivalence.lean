/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.RowLoopPrespectrum
public import Quillen.Waldhausen.SConstruction.Iterated.OmegaSpectrum
public import Quillen.Topology.HomotopyGroups.Loop.WeakEquivalence
public import Quillen.Topology.Prespectrum.StableEquivalence

/-!
# Stability of the actual distinguished-row comparison

The positive comparison levels are the unchanged original S-structure maps, whose complete
weak equivalence is already proved. Degree zero is their actual based-loop extension. Thus the
whole row-stabilization map is levelwise weak and induces isomorphisms in every stable degree.
No point-set inverse or equality with ordinary loop-tail stabilization is introduced.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u
namespace Quillen.Waldhausen.IteratedS

/-- Every actual row-stabilization level is a complete weak equivalence. -/
theorem rowStabilizationMap_weak (W : Model.{u}) (n : ℕ) :
    IsWeakHomotopyEquivalence ((rowStabilizationMap W).map n) := by
  cases n with
  | zero =>
    exact basedLoopMap_isWeakHomotopyEquivalence (stageLoopMap 0 W)
      (stageLoopMap_point 0 W) (stageLoopMap_weak 0 W)
  | succ k => exact stageLoopMap_weak k W

/-- The original actual row-stabilization map is stable in every integer degree. -/
theorem rowStabilizationMap_isStableEquivalence (W : Model.{u}) :
    LoopPrespectrum.IsStableEquivalence (rowStabilizationMap W) :=
  LoopPrespectrum.isStableEquivalence_of_levelwise _ (rowStabilizationMap_weak W)

end Quillen.Waldhausen.IteratedS
