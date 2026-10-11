/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.DoubleMappingCylinder.GapCollarComparison
public import Quillen.Topology.DoubleMappingCylinder.CollarGapConnectivity
public import Quillen.Topology.HomotopyGroups.Connectivity.HomotopySquare

/-!
# Finite homotopy excision for the actual original double-cylinder gap

If the original attaching maps f and g are p- and q-connected, the canonical original gap
`a ↦ (g(a), f(a), t ↦ l(a,t))` is r-connected whenever r+1≤p+q. The proof transfers genuine
open-cover excision through the actual band section, endpoint collar equivalences, and explicit
original cylinder-time homotopy. Fixed cuts and their midpoint remove all auxiliary choices
from the theorem's hypotheses. No separation, CW type or attaching-map cofibration is assumed.
The conclusion includes every target component and every actual fiber basepoint. Reduced
base-line collapse and stable cofiber excision remain distinct point-set and stabilization steps.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory
open scoped Topology unitInterval

universe u

namespace Quillen.DoubleCylinder

/-- The original full-cylinder gap satisfies the finite excision range. The exact original
pushout, attaching maps and full stored paths remain in the conclusion. -/
theorem gap_isHomotopyConnectedMap {A B C D : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
    {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
    (sq : IsPushout (Quillen.intervalEndpoints A) (endMap f g) l e)
    (p q r : ℕ) (hr : r + 1 ≤ p + q)
    (hf : IsHomotopyConnectedMap f.hom p) (hg : IsHomotopyConnectedMap g.hom q) :
    IsHomotopyConnectedMap (gap f g sq) r := by
  let lo : unitInterval := ⟨1 / 3, by constructor <;> norm_num⟩
  let hi : unitInterval := ⟨2 / 3, by constructor <;> norm_num⟩
  have hcut : lo < hi := by change (1 / 3 : ℝ) < 2 / 3; norm_num
  have hhi : 0 < hi := lt_of_le_of_lt bot_le hcut
  have hlo : lo < 1 := lt_of_lt_of_le hcut le_top
  let c := bandMidpoint lo hi hcut
  let source := gapOverlapEquiv f g sq lo hi c
  let target := gapTargetCollarEquiv f g sq lo hi hhi hlo
  exact IsHomotopyConnectedMap.of_weak_homotopy_square source.toFun target.toFun
    (gapCollarHomotopy f g sq lo hi c hhi hlo)
    (isWeakHomotopyEquivalence_of_homotopyEquiv source)
    (isWeakHomotopyEquivalence_of_homotopyEquiv target) r
    (collarGap_isHomotopyConnectedMap f g sq lo hi hcut p q r hr hf hg)

end Quillen.DoubleCylinder
