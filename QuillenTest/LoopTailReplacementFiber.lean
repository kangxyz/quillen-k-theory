/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.LoopTailReplacementFiberEquivalence

/-!
# Original-map consumers of replacement fiber preservation

The exact initial triangle, original fiber paths, independent homotopy/loop/cylinder parameters,
arbitrary-component class lifts and reflection, and original signed stable-class formula are
retained. Only the original source and target levels carry T1 hypotheses.
-/

@[expose] public section

noncomputable section

open CategoryTheory Quillen Quillen.LoopPrespectrum
open scoped Topology unitInterval

universe u

namespace QuillenTest.LoopTailReplacementFiber

open Quillen

/-- The initial fiber comparison sends the whole original fiber path through the original unit. -/
theorem original_initial_fiber_path {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    (k : ℕ) (z : (homotopyFiber f).space k) (r : unitInterval) :
    ((loopTailReplacementFiberComparison f).map k
      ((loopTailReplacementInclusion (homotopyFiber f)).map k z)).1.2 r =
        (loopTailReplacementInclusion F).map k (z.1.2 r) := rfl

/-- On a first-loop cylinder, homotopy time, cylinder height, and loop time remain independent. -/
theorem original_first_loop_homotopy_cylinder {E F : LoopPrespectrum.{u}}
    {f g : E ⟶ F} (H : Homotopy f g) (k : ℕ) (r s : unitInterval)
    (γ : Path (E.point (k + 1)) (E.point (k + 1))) :
    (loopTailReplacementHomotopy H).level k
      (r, Telescope.cylinder (loopTailIterate E) (loopTailTransition E) k 1 (s, γ)) =
        Telescope.cylinder (loopTailIterate F) (loopTailTransition F) k 1
          (s, H.loopTail.level k (r, γ)) := rfl

/-- The original loop coordinate inside the previous consumer is not transposed with time. -/
theorem original_loop_homotopy_parameters {E F : LoopPrespectrum.{u}} {f g : E ⟶ F}
    (H : Homotopy f g) (k : ℕ) (r t : unitInterval)
    (γ : Path (E.point (k + 1)) (E.point (k + 1))) :
    Path.toContinuousMap (H.loopTail.level k (r, γ)) t = H.level (k + 1) (r, γ t) := rfl

/-- The unchanged signed stable class maps through the literal initial triangle. -/
theorem original_signed_initial_class {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    (d : ℤ) (a : stableHomotopyGroup (homotopyFiber f) d) :
    (stableHomotopyFunctor d).map (loopTailReplacementFiberComparison f)
      ((stableHomotopyFunctor d).map (loopTailReplacementInclusion (homotopyFiber f)) a) =
        (stableHomotopyFunctor d).map (homotopyFiberMap (loopTailReplacementUnitSquare f)) a := by
  have h := congrArg (stableHomotopyFunctor d).map (loopTailReplacementFiberComparison_initial f)
  rw [Functor.map_comp] at h
  exact ConcreteCategory.congr_hom h a

/-- The actual signed boundary is preserved on each original target class. -/
theorem original_signed_connecting_class {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    (d : ℤ) (b : stableHomotopyGroup F (d + 1)) :
    (stableHomotopyFunctor d).map (loopTailReplacementFiberComparison f)
      ((stableHomotopyFunctor d).map (loopTailReplacementInclusion (homotopyFiber f))
        (stableFiberConnecting f d b)) =
      stableFiberConnecting (loopTailReplacementMap f) d
        ((stableHomotopyFunctor (d + 1)).map (loopTailReplacementInclusion F) b) :=
  ConcreteCategory.congr_hom (loopTailReplacementFiberComparison_connecting f d) b

variable {E F : LoopPrespectrum.{u}} [∀ k, T1Space (E.space k)] [∀ k, T1Space (F.space k)]
    (f : E ⟶ F)

/-- Every actual target fiber point is covered up to a genuine path by the original comparison. -/
theorem original_fiber_target_component (k : ℕ)
    (y : (homotopyFiber (loopTailReplacementMap f)).space k) :
    ∃ x : (loopTailReplacement (homotopyFiber f)).space k,
      Nonempty (Path ((loopTailReplacementFiberComparison f).map k x) y) :=
  (loopTailReplacementFiberComparison_isWeakHomotopyEquivalence f k).component_surjective y

/-- Any finite-degree class at the image of an arbitrary actual source point lifts. -/
theorem original_fiber_arbitrary_point_lift (k n : ℕ)
    (x : (loopTailReplacement (homotopyFiber f)).space k)
    (b : HomotopyGroup.Pi n ((homotopyFiber (loopTailReplacementMap f)).space k)
      ((loopTailReplacementFiberComparison f).map k x)) :
    ∃ a : HomotopyGroup.Pi n ((loopTailReplacement (homotopyFiber f)).space k) x,
      homotopyGroupMap ((loopTailReplacementFiberComparison f).map k) rfl a = b :=
  ((loopTailReplacementFiberComparison_isWeakHomotopyEquivalence f k).homotopy_bijective
    x n).surjective b

/-- Equality at any original source component is reflected, including degree zero. -/
theorem original_fiber_arbitrary_point_reflection (k n : ℕ)
    (x : (loopTailReplacement (homotopyFiber f)).space k)
    (a b : HomotopyGroup.Pi n ((loopTailReplacement (homotopyFiber f)).space k) x)
    (hab : homotopyGroupMap ((loopTailReplacementFiberComparison f).map k) rfl a =
      homotopyGroupMap ((loopTailReplacementFiberComparison f).map k) rfl b) : a = b :=
  ((loopTailReplacementFiberComparison_isWeakHomotopyEquivalence f k).homotopy_bijective
    x n).injective hab

end QuillenTest.LoopTailReplacementFiber
