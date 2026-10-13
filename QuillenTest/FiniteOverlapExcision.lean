/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.DoubleMappingCylinder.CollarGapConnectivity

/-!
# Actual finite excision, arbitrary fiber points and complete boundary tracks

The consumers retain the original collar comparison, arbitrary target and fiber points,
asymmetric zero bounds and the endpoint homotopy-degree range. The full HELP consumer recovers
every specified boundary path value, not merely its endpoints or homotopy class.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory
open scoped Topology unitInterval

universe u

namespace QuillenTest.FiniteOverlapExcision

open Quillen

/-- Every actual fiber point has the proved finite homotopy bound, including degree zero. -/
theorem original_overlap_fiber_homotopy {Y : Type u} [TopologicalSpace Y]
    (U V : Set Y) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (p q r : ℕ) (hr : r + 1 ≤ p + q)
    (hUV : IsHomotopyConnectedMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C({y : U // y.val ∈ V}, U)) p)
    (hVU : IsHomotopyConnectedMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C({y : V // y.val ∈ U}, V)) q)
    (y : HomotopyPullback (ContinuousMap.subtypeVal U) (ContinuousMap.subtypeVal V))
    (z : HomotopyFiber (HomotopyPullback.overlapComparison U V) y) (k : ℕ) (hk : k < r)
    (a b : HomotopyGroup.Pi k (HomotopyFiber (HomotopyPullback.overlapComparison U V) y) z) :
    a = b :=
  (HomotopyPullback.overlapComparison_isHomotopyConnectedMap U V hU hV hcover
    p q r hr hUV hVU).fiber_subsingleton y z k hk |>.elim a b

/-- The exact finite endpoint degree is surjective on the original homotopy-set map. -/
theorem original_overlap_endpoint_degree {Y : Type u} [TopologicalSpace Y]
    (U V : Set Y) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (p q r : ℕ) (hr : r + 1 ≤ p + q)
    (hUV : IsHomotopyConnectedMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C({y : U // y.val ∈ V}, U)) p)
    (hVU : IsHomotopyConnectedMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C({y : V // y.val ∈ U}, V)) q)
    (x : ↥(U ∩ V)) :
    Function.Surjective (homotopyGroupMap (N := Fin r)
      (HomotopyPullback.overlapComparison U V) (x := x) rfl) :=
  (HomotopyPullback.overlapComparison_isHomotopyConnectedMap U V hU hV hcover
    p q r hr hUV hVU).homotopyGroupMap_surjective x r le_rfl

/-- The asymmetric p=0, q=1 case still proves actual target-component coverage. -/
theorem original_collar_zero_left_coverage {A B C D : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
    {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
    (sq : IsPushout (Quillen.intervalEndpoints A) (DoubleCylinder.endMap f g) l e)
    (lo hi : unitInterval) (hcut : lo < hi)
    (hf : IsHomotopyConnectedMap f.hom 0) (hg : IsHomotopyConnectedMap g.hom 1)
    (y : HomotopyPullback
      (ContinuousMap.subtypeVal (DoubleCylinder.leftCollarSet f g sq hi))
      (ContinuousMap.subtypeVal (DoubleCylinder.rightCollarSet f g sq lo))) :
    Nonempty (HomotopyFiber (HomotopyPullback.overlapComparison
      (DoubleCylinder.leftCollarSet f g sq hi) (DoubleCylinder.rightCollarSet f g sq lo)) y) :=
  (DoubleCylinder.collarGap_isHomotopyConnectedMap f g sq lo hi hcut 0 1 0
    (by omega) hf hg).fiber_nonempty y

/-- Original finite attaching bounds yield the full prescribed boundary homotopy in the
actual collar gap, at every original boundary point and every original time. -/
theorem original_collar_gap_full_boundary_track {A B C D : TopCat.{u}}
    (f : A ⟶ B) (g : A ⟶ C)
    {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
    (sq : IsPushout (Quillen.intervalEndpoints A) (DoubleCylinder.endMap f g) l e)
    (lo hi : unitInterval) (hcut : lo < hi) (p q r m : ℕ)
    (hr : r + 1 ≤ p + q) (hm : m ≤ r)
    (hf : IsHomotopyConnectedMap f.hom p) (hg : IsHomotopyConnectedMap g.hom q)
    (a : C(CubicalTests.boundary.{u} m,
      ↥(DoubleCylinder.leftCollarSet f g sq hi ∩ DoubleCylinder.rightCollarSet f g sq lo)))
    (b : C(CubicalTests.cube.{u} m, HomotopyPullback
      (ContinuousMap.subtypeVal (DoubleCylinder.leftCollarSet f g sq hi))
      (ContinuousMap.subtypeVal (DoubleCylinder.rightCollarSet f g sq lo))))
    (H : ((HomotopyPullback.overlapComparison (DoubleCylinder.leftCollarSet f g sq hi)
      (DoubleCylinder.rightCollarSet f g sq lo)).comp a).Homotopy
        (b.comp (CubicalTests.boundaryInclusion m).hom)) :
    ∃ c : C(CubicalTests.cube.{u} m,
      ↥(DoubleCylinder.leftCollarSet f g sq hi ∩ DoubleCylinder.rightCollarSet f g sq lo)),
      c.comp (CubicalTests.boundaryInclusion m).hom = a ∧
      ∃ K : ((HomotopyPullback.overlapComparison (DoubleCylinder.leftCollarSet f g sq hi)
        (DoubleCylinder.rightCollarSet f g sq lo)).comp c).Homotopy b,
        ∀ t z, K (t, z.val) = H (t, z) :=
  (DoubleCylinder.collarGap_isHomotopyConnectedMap f g sq lo hi hcut p q r hr hf hg).cube_fullHELP
    m hm a b H

end QuillenTest.FiniteOverlapExcision
