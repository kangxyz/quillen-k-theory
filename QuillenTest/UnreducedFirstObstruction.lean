/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyCofiber.UnreducedFirstObstruction

/-! # The degree-two boundary and the unchanged cone cylinder -/
@[expose] public section
noncomputable section
open Quillen Quillen.ReducedMappingCone
open scoped Topology unitInterval
universe u

namespace QuillenTest.UnreducedFirstObstruction
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [SimplyConnectedSpace X] [SimplyConnectedSpace Y] (f : C(X, Y)) (x : X)

/-- Relative degree two does not silently require a commutative fiber fundamental group. -/
theorem degree_two_bijective :
    Function.Bijective (piMap 0 (unreducedFirstObstructionMap f (f x))
      (unreducedFirstObstructionMap_basepoint f x (f x) rfl)) :=
  unreducedFirstObstructionMap_pi_bijective f x (f x) rfl 0
    (isHomotopyConnectedMap_one_of_simplyConnected f x)

omit [SimplyConnectedSpace X] [SimplyConnectedSpace Y] in
/-- Even at the distinguished point, the inner stored path is the full original cylinder. -/
theorem degree_two_cylinder_track (t : unitInterval) :
    (unreducedFirstObstructionMap f (f x) (HomotopyFiber.basepoint f (f x) x rfl)).1.1.1.2 t =
      unreducedCylinder f (x, ULift.up t) := rfl

/-- The degree-two obstruction is recovered from its actual cone class. -/
theorem degree_two_round_trip
    (a : HomotopyGroup.Pi 1 (HomotopyFiber f (f x))
      (HomotopyFiber.basepoint f (f x) x rfl)) :
    (firstObstructionEquivCone f x 0 (isHomotopyConnectedMap_one_of_simplyConnected f x)).symm
      (firstObstructionEquivCone f x 0 (isHomotopyConnectedMap_one_of_simplyConnected f x) a) = a :=
  Equiv.symm_apply_apply _ _

omit [SimplyConnectedSpace X] [SimplyConnectedSpace Y] in
/-- Unit correction keeps the original cylinder prefix and changes only its final delay. -/
theorem degree_two_unit_track (t s : unitInterval) :
    (HomotopyFiber.loopsToIteratedFiberPathUnitPath
      (unreducedInclusion f) (unreducedVertex f) (f x)
      (HomotopyFiber.toPath (unreducedInclusion f) (unreducedVertex f)
        (unreducedFiberComparison f x)) t).1.1.1.2 s =
      Path.delayReflRight t
        (HomotopyFiber.toPath (unreducedInclusion f) (unreducedVertex f)
          (unreducedFiberComparison f x)) s := rfl

end QuillenTest.UnreducedFirstObstruction
