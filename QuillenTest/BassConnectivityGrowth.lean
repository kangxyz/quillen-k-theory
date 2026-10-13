/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassConnectivity

/-!
# Original-map consumers of finite Bass connectivity growth

The original double cylinder, arbitrary compact-open loops, actual coefficient maps and
iterated Laurent seed transitions retain their literal points and paths. The smallest proved
high-level cutoff and every finite offset are tested without assuming later-stage growth.
-/
@[expose] public section
noncomputable section
open CategoryTheory Limits MonoidalCategory AlgebraicGeometry
universe u
namespace QuillenTest.BassConnectivityGrowth

open Quillen
open PerfectComplexes

/-- The original unreduced cylinder has nonempty point-map fibers with the full endpoint bound.
-/
theorem original_cylinder_point_fiber
    {A B C D : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
    {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
    (sq : IsPushout (Quillen.intervalEndpoints A) (DoubleCylinder.endMap f g) l e)
    (a₀ : A) (n : ℕ)
    (hA : ∀ a k, k < n + 2 → Subsingleton (HomotopyGroup.Pi k A a))
    (hB : ∀ b k, k < n + 2 → Subsingleton (HomotopyGroup.Pi k B b))
    (hC : ∀ c k, k < n + 2 → Subsingleton (HomotopyGroup.Pi k C c))
    (z : HomotopyFiber (ContinuousMap.const D (PUnit.unit : PUnit.{u + 1})) PUnit.unit) :
    Subsingleton (HomotopyGroup.Pi (n + 1)
      (HomotopyFiber (ContinuousMap.const D (PUnit.unit : PUnit.{u + 1})) PUnit.unit) z) :=
  (isHomotopyConnectedMap_const_of_vanishing (DoubleCylinder.gapLeftEndpoint e (f a₀))
    (n + 2) (DoubleCylinder.homotopyGroup_subsingleton f g sq a₀ n hA hB hC)).fiber_subsingleton
      PUnit.unit z (n + 1) (by omega)

/-- Arbitrary original loop components retain the exact one-degree shift, including degree zero.
-/
theorem original_loop_component_bound {X : Type u} [TopologicalSpace X]
    (x : X) (n : ℕ) (h : Subsingleton (HomotopyGroup.Pi (n + 1) X x))
    (γ : Path x x) (a b : HomotopyGroup.Pi n (Path x x) γ) : a = b :=
  (subsingleton_pi_loop_of_succ x n h γ).elim a b

/-- At the actual cutoff i+2 every pair of original Bass-stage points is joined by a path. -/
theorem original_stage_cutoff_paths (i : ℕ) (R : CommRingCat.{u})
    (x y : ((boundedFlatAffineSectionBassDiagram i).obj R).space (i + 2)) : Joined x y := by
  let := pathConnectedSpace_of_subsingleton_pi_zero x
    (boundedFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_of_le
      i R (i + 2) le_rfl 0 (by omega) x)
  exact PathConnectedSpace.joined x y

/-- Literal coefficient maps have the proved bound at arbitrary actual fiber points. -/
theorem original_coefficient_fiber_bound (i : ℕ) {R S : CommRingCat.{u}} (f : R ⟶ S)
    (n k : ℕ) (hk : k < n + 1)
    (y : ((boundedFlatAffineSectionBassDiagram i).obj S).space (n + i + 2))
    (z : HomotopyFiber (((boundedFlatAffineSectionBassDiagram i).map f).map (n + i + 2)) y) :
    Subsingleton (HomotopyGroup.Pi k
      (HomotopyFiber (((boundedFlatAffineSectionBassDiagram i).map f).map (n + i + 2)) y) z) :=
  (boundedFlatAffineSectionBassDiagram_map_isHomotopyConnectedMap
    i R S ((boundedFlatAffineSectionBassDiagram i).map f) n).fiber_subsingleton y z k hk

/-- The same original iterated seed covers every successor target component above its cutoff. -/
theorem original_transition_component_coverage (i : ℕ) (R : CommRingCat.{u}) (n : ℕ)
    (y : ((boundedFlatAffineSectionBassDiagram (i + 1)).obj R).space (n + i + 3)) :
    ∃ x, Joined (((boundedFlatAffineSectionBassTransition i).app R).map (n + i + 3) x) y :=
  (boundedFlatAffineSectionBassTransition_isHomotopyConnectedMap i R n).component_surjective y

/-- The unchanged seed-induced homotopy map is surjective at the finite range endpoint. -/
theorem original_transition_endpoint_surjectivity (i : ℕ) (R : CommRingCat.{u}) (n : ℕ)
    (x : ((boundedFlatAffineSectionBassDiagram i).obj R).space (n + i + 3)) :
    Function.Surjective (homotopyGroupMap (N := Fin (n + 1))
      (((boundedFlatAffineSectionBassTransition i).app R).map (n + i + 3)) (x := x) rfl) :=
  IsHomotopyConnectedMap.homotopyGroupMap_surjective
    (boundedFlatAffineSectionBassTransition_isHomotopyConnectedMap i R n) x (n + 1) le_rfl

end QuillenTest.BassConnectivityGrowth
