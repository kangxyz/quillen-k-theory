/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.DoubleMappingCylinder.CollarConnectivity
public import Quillen.Topology.HomotopyPullback.OverlapConnectivity

/-!
# Finite connectivity of the original double-cylinder collar gap

The attaching maps f and g provide the two finite bounds through their actual strict midpoint
collar squares. Genuine open-cover excision then gives every all-point fiber bound for the
constant-path comparison of those original collars. Ordered height cuts suffice, and the bound
is r+1≤p+q. Comparison with the original full cylinder path from f(a) to g(a) is a separate step.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory
open scoped Topology unitInterval

universe u

namespace Quillen.DoubleCylinder

/-- Actual finite collar-gap connectivity from only the original attaching-map bounds. -/
theorem collarGap_isHomotopyConnectedMap {A B C D : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
    {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
    (sq : IsPushout (Quillen.intervalEndpoints A) (endMap f g) l e)
    (lo hi : unitInterval) (hcut : lo < hi) (p q r : ℕ) (hr : r + 1 ≤ p + q)
    (hf : IsHomotopyConnectedMap f.hom p) (hg : IsHomotopyConnectedMap g.hom q) :
    IsHomotopyConnectedMap (HomotopyPullback.overlapComparison
      (leftCollarSet f g sq hi) (rightCollarSet f g sq lo)) r :=
  HomotopyPullback.overlapComparison_isHomotopyConnectedMap
    (leftCollarSet f g sq hi) (rightCollarSet f g sq lo)
    (leftCollar_isOpen f g sq hi) (rightCollar_isOpen f g sq lo)
    (collar_cover f g sq hi lo hcut) p q r hr
    (leftOverlapInclusion_isHomotopyConnectedMap_of_lt f g sq lo hi hcut p hf)
    (rightOverlapInclusion_isHomotopyConnectedMap_of_lt f g sq lo hi hcut q hg)

end Quillen.DoubleCylinder
