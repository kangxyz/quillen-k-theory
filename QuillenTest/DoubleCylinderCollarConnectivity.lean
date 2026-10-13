/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.DoubleMappingCylinder.CollarConnectivity
public import Quillen.Topology.HELP.Connectivity

/-!
# Original attaching maps supply finite collar HELP

These consumers retain every map of the actual cylinder pushout and use only the original
attaching-map connectivity. No separate overlap-connectivity assumption is introduced.
Arbitrary fiber points, zero-degree component coverage, and whole specified cube-boundary
tracks are retained.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits MonoidalCategory
open scoped Topology unitInterval

universe u

namespace QuillenTest.DoubleCylinderCollarConnectivity

open Quillen

open DoubleCylinder CubicalTests

variable {A B C D : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
    {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
    (sq : IsPushout (Quillen.intervalEndpoints A) (endMap f g) l e)
    (lo hi : unitInterval) (c : Band lo hi)
include c

/-- The unchanged left attaching map supplies full HELP for the actual overlap inclusion,
including the entire original boundary homotopy at its limiting dimension. -/
theorem original_left_collar_fullHELP (n : ℕ) (hf : IsHomotopyConnectedMap f.hom n)
    (a : C(boundary.{u} n, {z : LeftCollar f g sq hi // lo < height f g sq z.val}))
    (b : C(cube.{u} n, LeftCollar f g sq hi))
    (H : ((leftOverlapInclusion f g sq lo hi).comp a).Homotopy
      (b.comp (boundaryInclusion n).hom)) :
    ∃ v : C(cube.{u} n, {z : LeftCollar f g sq hi // lo < height f g sq z.val}),
      v.comp (boundaryInclusion n).hom = a ∧
      ∃ K : ((leftOverlapInclusion f g sq lo hi).comp v).Homotopy b,
        ∀ t z, K (t, z.val) = H (t, z) :=
  (leftOverlapInclusion_isHomotopyConnectedMap f g sq lo hi c n hf).cube_fullHELP
    n le_rfl a b H

/-- Even at connectivity zero, the original right attaching map covers every actual collar
component by an overlap point and an actual path to the given collar point. -/
theorem original_right_overlap_component_coverage (hg : IsHomotopyConnectedMap g.hom 0)
    (y : RightCollar f g sq lo) :
    ∃ z : {z : RightCollar f g sq lo // height f g sq z.val < hi}, Joined z.val y :=
  (rightOverlapInclusion_isHomotopyConnectedMap f g sq lo hi c 0 hg).component_surjective y

/-- The finite bound is valid at every original overlap-inclusion fiber point, not just a
constant-path basepoint. -/
theorem original_left_overlap_arbitrary_fiber (n : ℕ) (hf : IsHomotopyConnectedMap f.hom n)
    (y : LeftCollar f g sq hi) (z : HomotopyFiber (leftOverlapInclusion f g sq lo hi) y)
    (k : ℕ) (hk : k < n) :
    Subsingleton (HomotopyGroup.Pi k (HomotopyFiber (leftOverlapInclusion f g sq lo hi) y) z) :=
  (leftOverlapInclusion_isHomotopyConnectedMap f g sq lo hi c n hf).fiber_subsingleton y z k hk

/-- The original first coordinate of a displayed cylinder point is unchanged by the overlap
projection, independent of the chosen contraction point in the band. -/
theorem original_left_overlap_projection (x : A) (t : Band lo hi) :
    leftOverlapProjectionEquiv f g sq lo hi c (leftBandHomeomorph f g sq lo hi (x, t)) = x := by
  change ((leftBandHomeomorph f g sq lo hi).symm
    (leftBandHomeomorph f g sq lo hi (x, t))).1 = x
  rw [Homeomorph.symm_apply_apply]

omit c in
/-- For arbitrary ordered original cuts, both required collar bounds come from the original
attaching maps alone. The contraction point is the proved explicit midpoint, not caller data. -/
theorem original_ordered_collar_cuts (h : lo < hi) (p q : ℕ)
    (hf : IsHomotopyConnectedMap f.hom p) (hg : IsHomotopyConnectedMap g.hom q) :
    IsHomotopyConnectedMap (leftOverlapInclusion f g sq lo hi) p ∧
      IsHomotopyConnectedMap (rightOverlapInclusion f g sq lo hi) q :=
  ⟨leftOverlapInclusion_isHomotopyConnectedMap_of_lt f g sq lo hi h p hf,
    rightOverlapInclusion_isHomotopyConnectedMap_of_lt f g sq lo hi h q hg⟩

end QuillenTest.DoubleCylinderCollarConnectivity
