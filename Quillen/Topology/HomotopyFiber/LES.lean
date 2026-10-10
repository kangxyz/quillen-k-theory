/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.HomotopyGroups.Loop.FiberExactness

/-!
# The positive-degree homotopy-fiber long exact sequence

For an arbitrary based continuous map `f : X → Y`, this file constructs the
connecting homomorphisms `π_(n+2) Y → π_(n+1) HF(f)` from actual loop-space
currying and the concrete loop-to-fiber inclusion. It proves image-equals-kernel
at all three recurring positions of the positive-degree sequence.

This theorem concerns the explicit topological homotopy fiber. Applying it to
an algebraic localization problem still requires a genuine fiber-comparison
theorem for that problem. The pointed-set tail is separate.
-/
@[expose] public section


noncomputable section
universe u v
namespace Quillen.HomotopyFiber
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable (f : C(X, Y)) (y : Y) (x : X) (h : f x = y)

/-- The actual connecting homomorphism, obtained by currying into the target
loop space and then including loops into the concrete homotopy fiber. -/
def connectingHom (n : ℕ) :
    HomotopyGroup.Pi (n + 2) Y y →*
      HomotopyGroup.Pi (n + 1) (HomotopyFiber f y) (basepoint f y x h) :=
  (piMap n (loopInclusion f y x h) (loopInclusion_refl f y x h)).comp
    (loopShiftMulEquiv (x := y) n).toMonoidHom

/-- Exactness at the homotopy groups of the homotopy fiber. -/
theorem range_connectingHom_eq_ker_projection (n : ℕ) :
    (connectingHom f y x h n).range =
      (piMap n (projection f y) (projection_basepoint f y x h)).ker := by
  rw [← piMap_range_loopInclusion_eq_ker_projection f y x h n]
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨b, rfl⟩
    refine ⟨(loopShiftMulEquiv (x := y) n).symm b, ?_⟩
    exact congrArg (piMap n (loopInclusion f y x h) (loopInclusion_refl f y x h))
      ((loopShiftMulEquiv (x := y) n).apply_symm_apply b)

/-- Exactness at the target homotopy group, proved from loop-space exactness
and naturality of the actual degree-shift isomorphism. -/
theorem range_piMap_eq_ker_connectingHom (n : ℕ) :
    (piMap (n + 1) f h).range = (connectingHom f y x h n).ker := by
  ext a
  change a ∈ (piMap (n + 1) f h).range ↔ connectingHom f y x h n a = 1
  constructor
  · rintro ⟨b, rfl⟩
    change piMap n (loopInclusion f y x h) (loopInclusion_refl f y x h)
      (loopShiftEquiv (n + 1) (homotopyGroupMap f h b)) = 1
    have hn := loopShiftEquiv_natural (n + 1) f h b
    refine (congrArg (piMap n (loopInclusion f y x h) (loopInclusion_refl f y x h)) hn).trans ?_
    exact congrArg (fun k : HomotopyGroup.Pi (n + 1) (Path x x) (Path.refl x) →*
      HomotopyGroup.Pi (n + 1) (HomotopyFiber f y) (basepoint f y x h) =>
        k (loopShiftEquiv (n + 1) b))
      (homotopyGroupMapHom_loopMap_inclusion_comp f y x h)
  · intro ha
    have hrange : loopShiftEquiv (n + 1) a ∈
        (piMap n (basedLoopMap f h) (basedLoopMap_refl f h)).range := by
      rw [piMap_range_loopMap_eq_ker_loopInclusion f y x h n]
      exact ha
    obtain ⟨b, hb⟩ := hrange
    refine ⟨(loopShiftMulEquiv (x := x) n).symm b, ?_⟩
    apply (loopShiftMulEquiv (x := y) n).injective
    exact (loopShiftEquiv_natural (n + 1) f h
      ((loopShiftMulEquiv (x := x) n).symm b)).trans
        ((congrArg (piMap n (basedLoopMap f h) (basedLoopMap_refl f h))
          ((loopShiftMulEquiv (x := x) n).apply_symm_apply b)).trans hb)

/-- All three recurring exactness positions of the positive-degree homotopy-fiber
long exact sequence, with the actual maps and homotopy groups. -/
theorem positiveLongExactSequence (n : ℕ) :
    (piMap (n + 1) f h).range = (connectingHom f y x h n).ker ∧
    (connectingHom f y x h n).range =
      (piMap n (projection f y) (projection_basepoint f y x h)).ker ∧
    (piMap n (projection f y) (projection_basepoint f y x h)).range = (piMap n f h).ker :=
  ⟨range_piMap_eq_ker_connectingHom f y x h n,
    range_connectingHom_eq_ker_projection f y x h n,
    piMap_range_projection_eq_ker f y x h n⟩

end Quillen.HomotopyFiber
