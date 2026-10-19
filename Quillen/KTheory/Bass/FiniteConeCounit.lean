/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.FiniteConeTopology
public import Quillen.Topology.Prespectrum.SuspensionLoopCounitStable

/-!
# Actual suspension-loop counits at finite Model cone stages

The same unlooped cones used by the original cone action, followed by any finite number of
parameter loops, satisfy the actual counit's excision conditions. Every topology and all-point
growth premise is supplied by the initial genuine Model diagram. No later cone is a Model,
and no telescope transition or classical-presentation identification is asserted.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum
open Quillen.LoopPrespectrum.FiniteParameterLooping
open Quillen.Waldhausen.IteratedS
universe u v w
namespace Quillen.KTheory.Bass.FiniteConeTopology
variable {C : Type u} [Category.{v} C]

/-- The actual counit at every finite cone-loop Model stage needs no additional hypotheses. -/
theorem modelLoopsIterate_suspensionLoopCounit_isStableEquivalence
    (Q : C ⥤ Arrow (Arrow C)) (i j : ℕ) (F : C ⥤ Model.{w}) (X : C) :
    IsStableEquivalence
      (suspensionLoopCounit (loops j ((iterate Q i (F ⋙ prespectrumFunctor)).obj X))) :=
  suspensionLoopCounit_isStableEquivalence_of_linearGrowth _ j
    (modelLoopsIterate_point_homotopyExtensionProperty Q i j F X)
    (fun n x k hk ↦ modelLoopsIterate_homotopyGroup_subsingleton Q i j F X n k hk x)

/-- The parameter-looped counit retains its actual forward direction at each finite stage. -/
theorem modelLoopsIterate_parameterLoopingCounit_isStableEquivalence
    (Q : C ⥤ Arrow (Arrow C)) (i j : ℕ) (F : C ⥤ Model.{w}) (X : C) :
    IsStableEquivalence (parameterLoopingMap
      (suspensionLoopCounit (loops j ((iterate Q i (F ⋙ prespectrumFunctor)).obj X)))) :=
  parameterLooping_suspensionLoopCounit_isStableEquivalence _
    (modelLoopsIterate_suspensionLoopCounit_isStableEquivalence Q i j F X)

end Quillen.KTheory.Bass.FiniteConeTopology
