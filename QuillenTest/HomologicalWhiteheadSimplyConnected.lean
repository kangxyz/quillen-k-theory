/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.HomologicalWhiteheadSimplyConnected

/-! Named regressions retain relative degree two, all actual fiber points,
range-zero component coverage, and the original ordinary singular map. -/

@[expose] public section
noncomputable section
open CategoryTheory Limits
universe u
namespace QuillenTest.HomologicalWhiteheadSimplyConnected

open Quillen
open LocalCoefficients
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- Positive connectivity proves actual path connectedness of every fiber. -/
theorem every_fiber_pathConnected (f : C(X, Y)) (hf : IsHomotopyConnectedMap f 1)
    (y : Y) : PathConnectedSpace (HomotopyFiber f y) :=
  hf.fiber_pathConnectedSpace y

variable [SimplyConnectedSpace X] [SimplyConnectedSpace Y]

/-- At the first induction step the killed group is the genuine fiber Pi1. -/
theorem first_relative_degree_two (f : C(X, Y)) (x : X)
    (hH : QuasiIso (pushforwardChainMap f (constant Y integralCoefficientModule.{u}))) :
    Subsingleton (HomotopyGroup.Pi 1 (HomotopyFiber f (f x))
      (HomotopyFiber.basepoint f (f x) x rfl)) :=
  ReducedMappingCone.subsingleton_firstObstruction_of_integral_quasiIso f x 0
    (isHomotopyConnectedMap_one_of_simplyConnected f x) hH

/-- The next range is valid at an arbitrary actual fiber point, not just the
constant-path canonical point of a source image. -/
theorem arbitrary_fiber_first_group (f : C(X, Y)) (x : X)
    (hH : QuasiIso (pushforwardChainMap f (constant Y integralCoefficientModule.{u})))
    (y : Y) (z : HomotopyFiber f y) :
    Subsingleton (HomotopyGroup.Pi 1 (HomotopyFiber f y) z) :=
  (ReducedMappingCone.isHomotopyConnectedMap_succ_of_integral_quasiIso f 0
    (isHomotopyConnectedMap_one_of_simplyConnected f x) hH).fiber_subsingleton y z 1 (by omega)

/-- The all-range conclusion retains actual nonempty fibers even in range zero. -/
theorem target_component_coverage (f : C(X, Y)) (x : X)
    (hH : QuasiIso (pushforwardChainMap f (constant Y integralCoefficientModule.{u})))
    (y : Y) : Nonempty (HomotopyFiber f y) :=
  (isHomotopyConnectedMap_of_integral_quasiIso f x hH 0).fiber_nonempty y

/-- The second positive fiber degree is included with the original basepoint. -/
theorem arbitrary_fiber_second_group (f : C(X, Y)) (x : X)
    (hH : QuasiIso (pushforwardChainMap f (constant Y integralCoefficientModule.{u})))
    (y : Y) (z : HomotopyFiber f y) :
    Subsingleton (HomotopyGroup.Pi 2 (HomotopyFiber f y) z) :=
  fiber_subsingleton_of_integral_quasiIso f x hH y z 2

/-- The actual coefficient object is the universe-correct lifted integers. -/
theorem integral_coefficient_carrier :
    integralCoefficientModule.{u} = ModuleCat.of ℤ (ULift.{u} ℤ) := rfl

/-- The ordinary singular-homology formulation concludes on the unchanged map. -/
theorem original_map_weak_equivalence (f : C(X, Y))
    (hH : ∀ n : ℕ, IsIso
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
        integralCoefficientModule.{u}).map (TopCat.ofHom f))) :
    IsWeakHomotopyEquivalence f :=
  isWeakHomotopyEquivalence_of_singularHomology_isIso f hH

end QuillenTest.HomologicalWhiteheadSimplyConnected
