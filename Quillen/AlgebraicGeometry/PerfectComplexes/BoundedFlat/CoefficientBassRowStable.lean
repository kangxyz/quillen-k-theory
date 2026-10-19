/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassFiniteStructure
public import Quillen.Topology.Prespectrum.StableFiniteRange
public import Quillen.Topology.Prespectrum.ParameterLoopingStableEquivalence

/-!
# Stability of the actual Bass-cone row refinement

The original cone structure has a proved finite range from its four genuine Model corners.
That range makes the unchanged whole row comparison stable in every integer degree. Its
explicit degree-zero extension and the row-compatible target structure are retained. The
parameter-looped comparison is therefore an actual stable roof leg for the normalized
first-row tensor cell and its prescribed whole null homotopy.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRowRefinement
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- The original whole comparison to the actual row-compatible cone target is stable. -/
theorem comparison_isStableEquivalence : IsStableEquivalence (comparison P a) := by
  apply isStableEquivalence_of_eventually_linearPi (comparison P a) 2 2
  intro n hn k hk
  change Function.Bijective (homotopyGroupMap (N := Fin (k + 2))
    ((source P a).structureMap (n + 1)) ((source P a).map_point (n + 1)))
  have h := source_structure_bijective P a (n - 2) k (by omega)
  rw [show n - 2 + 3 = n + 1 by omega] at h
  exact h

/-- The actual parameter-looped row comparison is stable in all signed degrees. -/
theorem parameterComparison_isStableEquivalence :
    IsStableEquivalence (parameterLoopingMap (comparison P a)) :=
  parameterLoopingMap_isStableEquivalence _ (comparison_isStableEquivalence P a)

end Quillen.PerfectComplexes.CoefficientBassRowRefinement
