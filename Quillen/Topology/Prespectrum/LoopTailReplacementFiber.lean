/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Prespectrum.LoopTailReplacementHomotopy
public import Quillen.Topology.Prespectrum.FiberNaturality

/-!
# The original loop-tail replacement comparison with path-space fibers

Applying the actual replacement to the whole original fiber nullhomotopy constructs a strict
map from the replacement of the fiber to the fiber of the replacement map. Its source coordinate,
whole fiber path, cylinder height, and literal triangle with the original initial inclusion are
retained. This construction has no separation or weak-equivalence hypothesis.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory
open scoped Topology unitInterval

universe u

namespace Quillen.LoopPrespectrum

variable {E F : LoopPrespectrum.{u}} (f : E ⟶ F)

/-- The replacement of the original fiber nullhomotopy keeps its entire continuous track. -/
def loopTailReplacementFiberNullHomotopy :
    Homotopy (loopTailReplacementMap (homotopyFiberProjection f) ≫ loopTailReplacementMap f)
      (zeroHom (loopTailReplacement (homotopyFiber f)) (loopTailReplacement F)) where
  level := (loopTailReplacementHomotopy (homotopyFiberNullHomotopy f)).level
  at_zero k x := by
    have h := (loopTailReplacementHomotopy (homotopyFiberNullHomotopy f)).at_zero k x
    exact h.trans (congrArg (fun q ↦ q.map k x)
      (loopTailReplacementMap_comp (homotopyFiberProjection f) f))
  at_one k x := by
    have h := (loopTailReplacementHomotopy (homotopyFiberNullHomotopy f)).at_one k x
    exact h.trans (congrArg (fun q ↦ q.map k x)
      (loopTailReplacementMap_zero (homotopyFiber f) F))
  at_point := (loopTailReplacementHomotopy (homotopyFiberNullHomotopy f)).at_point
  comm := (loopTailReplacementHomotopy (homotopyFiberNullHomotopy f)).comm

/-- The actual fiber lift of the original replacement nullhomotopy. -/
def loopTailReplacementFiberComparison :
    loopTailReplacement (homotopyFiber f) ⟶ homotopyFiber (loopTailReplacementMap f) :=
  homotopyFiberLift (loopTailReplacementMap f) (loopTailReplacementMap (homotopyFiberProjection f))
    (loopTailReplacementFiberNullHomotopy f)

/-- Projection recovers the unchanged replacement of the original fiber projection. -/
@[simp] theorem loopTailReplacementFiberComparison_projection :
    loopTailReplacementFiberComparison f ≫ homotopyFiberProjection (loopTailReplacementMap f) =
      loopTailReplacementMap (homotopyFiberProjection f) :=
  homotopyFiberLift_projection _ _ _

/-- The original source coordinate is preserved for every actual replacement point. -/
@[simp] theorem loopTailReplacementFiberComparison_source (k : ℕ)
    (z : (loopTailReplacement (homotopyFiber f)).space k) :
    ((loopTailReplacementFiberComparison f).map k z).1.1 =
      (loopTailReplacementMap (homotopyFiberProjection f)).map k z := rfl

/-- Fiber-path time and cylinder height remain independent at every original tower stage. -/
@[simp] theorem loopTailReplacementFiberComparison_cylinder_path (k i : ℕ)
    (r s : unitInterval) (z : (loopTailIterate (homotopyFiber f) i).space k) :
    ((loopTailReplacementFiberComparison f).map k
      (Telescope.cylinder (loopTailIterate (homotopyFiber f))
        (loopTailTransition (homotopyFiber f)) k i (s, z))).1.2 r =
      Telescope.cylinder (loopTailIterate F) (loopTailTransition F) k i
        (s, (loopTailIterateHomotopy (homotopyFiberNullHomotopy f) i).level k (r, z)) := rfl

/-- The original initial inclusions form their literal strict arrow square. -/
def loopTailReplacementUnitSquare : Arrow.mk f ⟶ Arrow.mk (loopTailReplacementMap f) :=
  Arrow.homMk (loopTailReplacementInclusion E) (loopTailReplacementInclusion F)
    (loopTailReplacementInclusion_naturality f).symm

/-- The comparison's triangle with the original unit commutes literally, including the whole
original fiber path rather than merely its homotopy class. -/
theorem loopTailReplacementFiberComparison_initial :
    loopTailReplacementInclusion (homotopyFiber f) ≫ loopTailReplacementFiberComparison f =
      homotopyFiberMap (loopTailReplacementUnitSquare f) := by
  apply Hom.ext
  funext k
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · rfl

/-- The actual signed connecting map commutes with the same comparison and original units.
The displayed factorization retains the original all-integer boundary orientation. -/
theorem loopTailReplacementFiberComparison_connecting (d : ℤ) :
    stableFiberConnecting f d ≫
        (stableHomotopyFunctor d).map (loopTailReplacementInclusion (homotopyFiber f)) ≫
          (stableHomotopyFunctor d).map (loopTailReplacementFiberComparison f) =
      (stableHomotopyFunctor (d + 1)).map (loopTailReplacementInclusion F) ≫
        stableFiberConnecting (loopTailReplacementMap f) d := by
  rw [← Functor.map_comp, loopTailReplacementFiberComparison_initial]
  exact (stableFiberConnecting_naturality (loopTailReplacementUnitSquare f) d).symm

end Quillen.LoopPrespectrum
