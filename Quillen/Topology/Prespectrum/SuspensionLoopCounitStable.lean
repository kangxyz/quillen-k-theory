/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.Prespectrum.SuspensionLoopCounit
public import Quillen.Topology.Prespectrum.ConeParameterLoopingExcision

/-!
# Stable counit from actual cone excision

The actual evaluation counit is stable when the original cone-to-fiber comparison for loops
to the point is stable. The supplied fiber lift is the proved point-fiber isomorphism, not a
stable-group surrogate. Closed well-based points and all-point linear growth discharge the
one excision premise at the explicit one-larger loop offset.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Quillen.LoopPrespectrum

/-- Original excision makes the unchanged suspension-loop evaluation counit stable. -/
theorem suspensionLoopCounit_isStableEquivalence (E : LoopPrespectrum.{u})
    (he : IsStableEquivalence
      (mappingConeFiberComparison (zeroHom (parameterLooping E) pointPrespectrum))) :
    IsStableEquivalence (suspensionLoopCounit E) := by
  apply mappingConeDesc_isStableEquivalence _ _ _ he
  rw [loopEvaluationHomotopy_fiberLift]
  intro d
  infer_instance

/-- All-point linear growth and the original point topology discharge the actual excision. -/
theorem suspensionLoopCounit_isStableEquivalence_of_linearGrowth
    (E : LoopPrespectrum.{u}) (c : ℕ) [∀ n, T1Space (E.space n)]
    (hE : ∀ n, Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (E.point n))))
    (hπ : ∀ n x k, k < n + 2 →
      Subsingleton (HomotopyGroup.Pi k (E.space (n + c + 2)) x)) :
    IsStableEquivalence (suspensionLoopCounit E) := by
  apply suspensionLoopCounit_isStableEquivalence
  apply mappingConeFiberComparison_isStableEquivalence_of_linearGrowth _ (c + 1)
  · intro n
    exact parameterLooping_point_homotopyExtensionProperty E _ isClosed_singleton (hE _)
  · intro n
    exact pointPrespectrum_point_homotopyExtensionProperty _
  · intro n
    rw [show n + (c + 1) + 2 = (n + 1) + c + 2 by omega]
    intro γ k hk
    exact Quillen.subsingleton_pi_loop_of_succ (E.point ((n + 1) + c + 2)) k
      (hπ (n + 1) (E.point _) (k + 1) (by omega)) γ
  · intro n x k _hk
    exact Quillen.subsingleton_pi_of_contractible k PUnit.{u + 1} x

/-- The actual parameter loop of the same counit is stable in the direction used by TT. -/
theorem parameterLooping_suspensionLoopCounit_isStableEquivalence
    (E : LoopPrespectrum.{u}) (he : IsStableEquivalence (suspensionLoopCounit E)) :
    IsStableEquivalence (parameterLoopingMap (suspensionLoopCounit E)) :=
  parameterLoopingMap_isStableEquivalence _ he

end Quillen.LoopPrespectrum
