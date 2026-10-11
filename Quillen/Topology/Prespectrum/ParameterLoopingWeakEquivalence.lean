/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.HomotopyGroups.Loop.WeakEquivalence
public import Quillen.Topology.Prespectrum.ParameterLooping
public import Quillen.Topology.Prespectrum.PositiveLevelEquivalence

/-!
# Weak invariance of actual parameter-correct looping

Complete weak equivalences on the original positive levels remain complete
weak equivalences after applying `parameterLoopingMap`. Consequently the
unchanged looped prespectrum map is a stable equivalence. The result does not
require connected loop spaces, separation, well-basedness, or an Omega axiom.
-/
@[expose] public section

noncomputable section
open CategoryTheory
universe u
namespace Quillen.LoopPrespectrum

/-- The unchanged parameter-correct loop map preserves complete weak equivalence
at every original positive level, including all loop components. -/
theorem parameterLoopingMap_positiveLevel_isWeakHomotopyEquivalence
    {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    (hf : ∀ n, IsWeakHomotopyEquivalence (f.map (n + 1))) (n : ℕ) :
    IsWeakHomotopyEquivalence ((parameterLoopingMap f).map (n + 1)) :=
  basedLoopMap_isWeakHomotopyEquivalence (f.map (n + 1)) (f.map_point (n + 1)) (hf n)

/-- Original positive-level weak equivalences induce a stable equivalence on the
actual parameter-correct looping, with no condition on the zeroth level. -/
theorem parameterLoopingMap_isStableEquivalence_of_positiveLevel
    {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    (hf : ∀ n, IsWeakHomotopyEquivalence (f.map (n + 1))) :
    IsStableEquivalence (parameterLoopingMap f) :=
  isStableEquivalence_of_positiveLevel _
    (parameterLoopingMap_positiveLevel_isWeakHomotopyEquivalence f hf)

end Quillen.LoopPrespectrum
