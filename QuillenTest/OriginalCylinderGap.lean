/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.DoubleMappingCylinder.GapConnectivity
public import Quillen.Topology.HELP.Connectivity

/-!
# Original full-cylinder gap excision consumers

The original attaching maps, cylinder path, midpoint deformation time and stored path time are
kept explicitly. Finite excision is tested at arbitrary fiber points, at an asymmetric zero bound,
and on a fully prescribed boundary homotopy including each of its stored target-path values.
-/

@[expose] public section

open Quillen.DoubleCylinder


noncomputable section

open CategoryTheory Limits MonoidalCategory
open scoped Topology unitInterval

universe u

namespace QuillenTest.OriginalCylinderGap

open Quillen

open DoubleCylinder

variable {A B C D : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
    {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
    (sq : IsPushout (Quillen.intervalEndpoints A) (endMap f g) l e)

/-- The gap retains both original endpoint images and the exact full original cylinder path. -/
theorem original_gap_coordinates (a : A) :
    (gap f g sq a).val.1 = g a ∧ (gap f g sq a).val.2.1 = f a ∧
      (gap f g sq a).val.2.2 =
        (⟨fun t ↦ l (a, ULift.up t), l.hom.continuous.comp (by fun_prop)⟩ : C(unitInterval, D)) :=
  ⟨rfl, rfl, rfl⟩

/-- The actual original cylinder-to-collar homotopy keeps both time variables and the
original source point; no representative or endpoint-only replacement is used. -/
theorem original_collar_square_path (lo hi : unitInterval) (hcut : lo < hi)
    (r t : unitInterval) (a : A) :
    (gapCollarHomotopy f g sq lo hi (bandMidpoint lo hi hcut)
      (lt_of_le_of_lt bot_le hcut) (lt_of_lt_of_le hcut le_top) (r, a)).val.2.2 t =
      l (a, ULift.up (Set.Icc.convexComb t (bandMidpoint lo hi hcut).val r)) := rfl

/-- Finite excision kills the indicated homotopy degree at every actual original gap-fiber
point, without restricting to a chosen component or a constant stored path. -/
theorem original_gap_fiber_homotopy (p q r k : ℕ) (hr : r + 1 ≤ p + q) (hk : k < r)
    (hf : IsHomotopyConnectedMap f.hom p) (hg : IsHomotopyConnectedMap g.hom q)
    (y : HomotopyPullback (gapLeftEndpoint e) (gapRightEndpoint e))
    (z : HomotopyFiber (gap f g sq) y)
    (a b : HomotopyGroup.Pi k (HomotopyFiber (gap f g sq) y) z) : a = b :=
  (gap_isHomotopyConnectedMap f g sq p q r hr hf hg).fiber_subsingleton y z k hk |>.elim a b

/-- The asymmetric zero bound still covers every target component for the full original gap. -/
theorem original_gap_zero_right_coverage
    (hf : IsHomotopyConnectedMap f.hom 1) (hg : IsHomotopyConnectedMap g.hom 0)
    (y : HomotopyPullback (gapLeftEndpoint e) (gapRightEndpoint e)) :
    ∃ a : A, Joined (gap f g sq a) y :=
  (gap_isHomotopyConnectedMap f g sq 1 0 0 (by omega) hf hg).component_surjective y

/-- The actual original source lift retains the whole supplied boundary homotopy and, in
particular, each stored target-path value at unrelated deformation and path times. -/
theorem original_gap_prescribed_boundary_paths (p q r m : ℕ)
    (hr : r + 1 ≤ p + q) (hm : m ≤ r)
    (hf : IsHomotopyConnectedMap f.hom p) (hg : IsHomotopyConnectedMap g.hom q)
    (a : C(CubicalTests.boundary.{u} m, A))
    (b : C(CubicalTests.cube.{u} m,
      HomotopyPullback (gapLeftEndpoint e) (gapRightEndpoint e)))
    (H : ((gap f g sq).comp a).Homotopy (b.comp (CubicalTests.boundaryInclusion m).hom)) :
    ∃ c : C(CubicalTests.cube.{u} m, A), c.comp (CubicalTests.boundaryInclusion m).hom = a ∧
      ∃ K : ((gap f g sq).comp c).Homotopy b,
        (∀ r z, K (r, z.val) = H (r, z)) ∧
          ∀ r (z : CubicalTests.boundary.{u} m) t,
            (K (r, z.val)).val.2.2 t = (H (r, z)).val.2.2 t := by
  obtain ⟨c, hc, K, hK⟩ := (gap_isHomotopyConnectedMap f g sq p q r hr hf hg).cube_fullHELP
    m hm a b H
  exact ⟨c, hc, K, hK, fun r z t ↦ congrArg (fun v ↦ v.val.2.2 t) (hK r z)⟩

end QuillenTest.OriginalCylinderGap
