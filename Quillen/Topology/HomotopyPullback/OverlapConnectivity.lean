/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyPullback.OverlapCubeLifting
public import Quillen.Topology.HELP.ConnectivityCriterion

/-!
# Finite homotopy excision for the original open-cover gap map

The actual overlap inclusions' p- and q-connectivity imply r-connectivity of the original
constant-path comparison whenever r+1≤p+q. Whole-grid normalization and continuous column
selection prove the strict cube problems; their exact HEP correction proves all actual fiber
bounds. The fixed disjoint parameter bands introduce no caller hypothesis. Fibers are nonempty
and their homotopy sets vanish in degrees k<r at every fiber point. In particular p=q=0 implies
no nonnegative range, while either asymmetric zero bound is retained. No target separation,
CW type, or inclusion-cofibration hypothesis is used.
-/

@[expose] public section

noncomputable section

open scoped Topology unitInterval

universe u

namespace Quillen.HomotopyPullback

/-- Genuine finite excision for the original constant-path gap of an open cover. -/
theorem overlapComparison_isHomotopyConnectedMap {Y : Type u} [TopologicalSpace Y]
    (U V : Set Y) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (p q r : ℕ) (hr : r + 1 ≤ p + q)
    (hUV : IsHomotopyConnectedMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C({y : U // y.val ∈ V}, U)) p)
    (hVU : IsHomotopyConnectedMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C({y : V // y.val ∈ U}, V)) q) :
    IsHomotopyConnectedMap (overlapComparison U V) r := by
  let lower : unitInterval := ⟨1 / 3, by constructor <;> norm_num⟩
  let upper : unitInterval := ⟨2 / 3, by constructor <;> norm_num⟩
  have hlow : (0 : unitInterval) < lower := by change (0 : ℝ) < 1 / 3; norm_num
  have hmid : lower ≤ upper := by change (1 / 3 : ℝ) ≤ 2 / 3; norm_num
  have hupp : upper < (1 : unitInterval) := by change (2 / 3 : ℝ) < 1; norm_num
  apply isHomotopyConnectedMap_of_cube_strictHELP (overlapComparison U V) r
  intro m hm a b w
  exact overlap_cube_strictHELP m p q (by omega) hU hV hcover hUV hVU a b w
    0 lower upper 1 hlow hmid hupp

end Quillen.HomotopyPullback
