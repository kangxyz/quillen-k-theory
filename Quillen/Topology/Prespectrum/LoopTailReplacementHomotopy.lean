/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.LoopTailReplacementFunctor
public import Quillen.Topology.Prespectrum.TelescopeHomotopy

/-!
# Actual coherent homotopies under loop-tail replacement

The untransposed loop-tail construction acts on whole coherent homotopies. The original
stabilization squares commute at every homotopy time, so the existing strict telescope homotopy
descends them without changing cylinder height. Original time slices, initial inclusions, and
zero maps are retained. These constructions need no separation or weak-equivalence hypothesis.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory
open scoped Topology unitInterval

universe u

namespace Quillen.LoopPrespectrum

variable {E F : LoopPrespectrum.{u}} {f g : E ⟶ F}

/-- Apply the actual untransposed loop-tail construction to a whole coherent homotopy. -/
def Homotopy.loopTail (H : Homotopy f g) :
    Homotopy (loopTailFunctor.map f) (loopTailFunctor.map g) where
  level k :=
    { toFun (z : unitInterval × Path (E.point (k + 1)) (E.point (k + 1))) :=
        { toFun t := H.level (k + 1) (z.1, z.2 t)
          continuous_toFun := by fun_prop
          source' := by rw [z.2.source]; exact H.at_point (k + 1) z.1
          target' := by rw [z.2.target]; exact H.at_point (k + 1) z.1 }
      continuous_toFun := by
        apply Path.continuous_uncurry_iff.mp
        change Continuous (fun z : (unitInterval × Path (E.point (k + 1))
          (E.point (k + 1))) × unitInterval ↦ H.level (k + 1) (z.1.1, z.1.2 z.2))
        fun_prop }
  at_zero k γ := by
    change Path (E.point (k + 1)) (E.point (k + 1)) at γ
    apply Path.ext
    funext t
    exact H.at_zero (k + 1) (γ t)
  at_one k γ := by
    change Path (E.point (k + 1)) (E.point (k + 1)) at γ
    apply Path.ext
    funext t
    exact H.at_one (k + 1) (γ t)
  at_point k r := by
    apply Path.ext
    funext t
    exact H.at_point (k + 1) r
  comm k r γ s := by
    change Path (E.point (k + 1)) (E.point (k + 1)) at γ
    apply Path.ext
    funext t
    exact H.comm (k + 1) r (γ s) t

/-- The homotopy time remains independent of the unchanged loop coordinate. -/
@[simp] theorem Homotopy.loopTail_apply (H : Homotopy f g) (k : ℕ)
    (r t : unitInterval) (γ : Path (E.point (k + 1)) (E.point (k + 1))) :
    Path.toContinuousMap (H.loopTail.level k (r, γ)) t = H.level (k + 1) (r, γ t) := rfl

/-- Every time slice is the original functor applied to the original time slice. -/
@[simp] theorem Homotopy.loopTail_at (H : Homotopy f g) (r : unitInterval) :
    H.loopTail.at r = loopTailFunctor.map (H.at r) := rfl

/-- Iterate the actual homotopy without changing any original time parameter. -/
def loopTailIterateHomotopy (H : Homotopy f g) :
    (i : ℕ) → Homotopy (loopTailIterateMap f i) (loopTailIterateMap g i)
  | 0 => H
  | i + 1 => (loopTailIterateHomotopy H i).loopTail

/-- The iterated homotopy's original time slices are the original iterated strict maps. -/
@[simp] theorem loopTailIterateHomotopy_at (H : Homotopy f g) (i : ℕ) (r : unitInterval) :
    (loopTailIterateHomotopy H i).at r = loopTailIterateMap (H.at r) i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    change (loopTailIterateHomotopy H i).loopTail.at r = _
    rw [Homotopy.loopTail_at, ih]
    rfl

/-- The strict stabilization square holds at every original homotopy time. -/
theorem loopTailIterateHomotopy_transition (H : Homotopy f g) (i k : ℕ)
    (r : unitInterval) (x : (loopTailIterate E i).space k) :
    (loopTailTransition F i).map k ((loopTailIterateHomotopy H i).level k (r, x)) =
      (loopTailIterateHomotopy H (i + 1)).level k (r, (loopTailTransition E i).map k x) := by
  apply Path.ext
  funext t
  exact ((loopTailIterateHomotopy H i).comm k r x t).symm

/-- The original cylinder-preserving telescope construction acts on whole coherent homotopies. -/
def loopTailReplacementHomotopy (H : Homotopy f g) :
    Homotopy (loopTailReplacementMap f) (loopTailReplacementMap g) :=
  Telescope.mapHomotopy (loopTailIterate E) (loopTailTransition E)
    (loopTailIterate F) (loopTailTransition F) (loopTailIterateMap f) (loopTailIterateMap g)
    (loopTailIterateMap_transition f) (loopTailIterateMap_transition g)
    (loopTailIterateHomotopy H) (loopTailIterateHomotopy_transition H)

/-- The whole original cylinder retains its height independently of the homotopy time. -/
@[simp] theorem loopTailReplacementHomotopy_cylinder (H : Homotopy f g) (k i : ℕ)
    (r s : unitInterval) (x : (loopTailIterate E i).space k) :
    (loopTailReplacementHomotopy H).level k
      (r, Telescope.cylinder (loopTailIterate E) (loopTailTransition E) k i (s, x)) =
        Telescope.cylinder (loopTailIterate F) (loopTailTransition F) k i
          (s, (loopTailIterateHomotopy H i).level k (r, x)) := rfl

/-- Every replacement time slice is exactly the original replacement map of that time slice. -/
theorem loopTailReplacementHomotopy_at (H : Homotopy f g) (r : unitInterval) :
    (loopTailReplacementHomotopy H).at r = loopTailReplacementMap (H.at r) := by
  apply Telescope.hom_ext
  intro k i s x
  change Telescope.cylinder (loopTailIterate F) (loopTailTransition F) k i
    (s, ((loopTailIterateHomotopy H i).at r).map k x) = _
  rw [loopTailIterateHomotopy_at]
  rfl

/-- The initial inclusion retains the whole original homotopy track pointwise. -/
@[simp] theorem loopTailReplacementHomotopy_initial (H : Homotopy f g) (k : ℕ)
    (r : unitInterval) (x : E.space k) :
    (loopTailReplacementHomotopy H).level k (r, (loopTailReplacementInclusion E).map k x) =
      (loopTailReplacementInclusion F).map k (H.level k (r, x)) := rfl

/-- The actual iterated strict map of a zero arrow is the original zero arrow. -/
@[simp] theorem loopTailIterateMap_zero (E F : LoopPrespectrum.{u}) (i : ℕ) :
    loopTailIterateMap (zeroHom E F) i = zeroHom (loopTailIterate E i) (loopTailIterate F i) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    change loopTailFunctor.map (loopTailIterateMap (zeroHom E F) i) = _
    rw [ih]
    rfl

/-- The reduced telescope's actual zero arrow collapses the entire original basepoint ray. -/
@[simp] theorem loopTailReplacementMap_zero (E F : LoopPrespectrum.{u}) :
    loopTailReplacementMap (zeroHom E F) = zeroHom (loopTailReplacement E) (loopTailReplacement F)
      := by
  apply Telescope.hom_ext
  intro k i s x
  change Telescope.cylinder (loopTailIterate F) (loopTailTransition F) k i
    (s, (loopTailIterateMap (zeroHom E F) i).map k x) = (loopTailReplacement F).point k
  rw [loopTailIterateMap_zero]
  exact Telescope.cylinder_point (loopTailIterate F) (loopTailTransition F) k i s

end Quillen.LoopPrespectrum
