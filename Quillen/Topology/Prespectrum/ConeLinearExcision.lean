/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.ConeFiberConnectivity
public import Quillen.Topology.Prespectrum.StableConnectivity
public import Quillen.Topology.HomotopyGroups.Connectivity.Vanishing
public import Quillen.Topology.HomotopyGroups.Connectivity.VanishingTransport

/-!
# Original cone excision from explicit all-point linear vanishing

For the unchanged prespectrum map, all-point vanishing below n+2 at level n+c+2 and HEP at
the two literal chosen points give finite cone-to-fiber range2*n+2. The original signed stable
colimit then gives stable excision with explicit cutoffc+1/loss2*c. These hypotheses can be
verified for actual model diagrams and propagated through their original finite Bass iterates.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Quillen.LoopPrespectrum
variable {E F : LoopPrespectrum.{u}} (f : E ⟶ F) (c : ℕ)

/-- The original cone-fiber comparison has its doubled range from all-point linear vanishing. -/
theorem mappingConeFiberComparison_isHomotopyConnectedMap_of_linearGrowth
    (n : ℕ)
    (hE : Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (E.point (n + c + 2)))))
    (hF : Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (F.point (n + c + 2)))))
    (hπE : ∀ x k, k < n + 2 →
      Subsingleton (HomotopyGroup.Pi k (E.space (n + c + 2)) x))
    (hπF : ∀ x k, k < n + 2 →
      Subsingleton (HomotopyGroup.Pi k (F.space (n + c + 2)) x)) :
    IsHomotopyConnectedMap ((mappingConeFiberComparison f).map (n + c + 2)) (2 * n + 2) := by
  let := pathConnectedSpace_of_subsingleton_pi_zero (F.point (n + c + 2)) (hπF _ 0 (by omega))
  exact mappingConeFiberComparison_level_isHomotopyConnectedMap f (n + c + 2) hE hF
    (n + 1) (n + 2) (2 * n + 2) (by omega)
    (isHomotopyConnectedMap_of_vanishing (f.map _) (E.point _) (n + 1)
      (fun x k hk ↦ hπE x k (by omega)) (fun x k hk ↦ hπF x k (by omega)))
    (isHomotopyConnectedMap_const_of_vanishing (E.point _) (n + 2) hπE)

/-- Explicit all-point linear growth proves genuine original stable cone-to-fiber excision. -/
theorem mappingConeFiberComparison_isStableEquivalence_of_linearGrowth
    (hE : ∀ n, Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (E.point (n + c + 2)))))
    (hF : ∀ n, Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (F.point (n + c + 2)))))
    (hπE : ∀ n x k, k < n + 2 →
      Subsingleton (HomotopyGroup.Pi k (E.space (n + c + 2)) x))
    (hπF : ∀ n x k, k < n + 2 →
      Subsingleton (HomotopyGroup.Pi k (F.space (n + c + 2)) x)) :
    IsStableEquivalence (mappingConeFiberComparison f) := by
  apply isStableEquivalence_of_eventually_linearConnectivity _ (c + 1) (2 * c)
  intro n hn
  have h := mappingConeFiberComparison_isHomotopyConnectedMap_of_linearGrowth f c
    (n - (c + 1)) (hE _) (hF _) (hπE _) (hπF _)
  rw [show n - (c + 1) + c + 2 = n + 1 by omega,
    show 2 * (n - (c + 1)) + 2 = 2 * n - 2 * c by omega] at h
  exact h

end Quillen.LoopPrespectrum
