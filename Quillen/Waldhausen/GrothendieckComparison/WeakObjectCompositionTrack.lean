/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.GrothendieckComparison.WeakObjectSquareTrack

/-!
# The original weak-arrow composition triangle as a loop-space path homotopy

The original two weak arrows and their literal composite give the entire comparison. Its
nerve endpoints are fixed original object loops for every triangle-comparison time. This
supplies the actual scalar factorization route in the localization boundary calculation.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Convexity
open scoped Topology
universe u v
namespace Quillen.Waldhausen.Structure
variable {C : Type u} [Category.{v} C] (W : Structure C)
  {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (hf : W.weq f) (hg : W.weq g)

/-- Curry the entire original weak-arrow square into its specified path of based loops. -/
def weakObjectSquareLoopPath : Path (W.kZeroObjectLoop A) (W.kZeroObjectLoop B) where
  toFun s := (W.weakObjectSquareTrack f hf).eval s
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    exact (W.weakObjectSquareTrack f hf).continuous
  source' := Path.Homotopy.eval_zero _
  target' := Path.Homotopy.eval_one _

/-- The initial nerve endpoint is fixed throughout the actual composition triangle. -/
theorem weakObjectCompositionCube_nerve_zero (r t : unitInterval) :
    W.weakObjectCompositionCube f g hf hg (r, 0, t) = W.kZeroObjectLoop A t := by
  have he : W.weakObjectCompositionCube f g hf hg (r, 0, t) =
      W.weakObjectCompositionCube f g hf hg (1, 0, t) := by
    change W.weakObjectCompositionRealization f g hf hg (_, SimplexCategory.toTopHomeo _ _) =
      W.weakObjectCompositionRealization f g hf hg (_, SimplexCategory.toTopHomeo _ _)
    rw [Path.Homotopy.source, Path.Homotopy.source]
  rw [he, weakObjectCompositionCube_one, weakObjectSquare_initial]

/-- The terminal nerve endpoint is the original target loop at every comparison time. -/
theorem weakObjectCompositionCube_nerve_one (r t : unitInterval) :
    W.weakObjectCompositionCube f g hf hg (r, 1, t) = W.kZeroObjectLoop D t := by
  have he : W.weakObjectCompositionCube f g hf hg (r, 1, t) =
      W.weakObjectCompositionCube f g hf hg (1, 1, t) := by
    change W.weakObjectCompositionRealization f g hf hg (_, SimplexCategory.toTopHomeo _ _) =
      W.weakObjectCompositionRealization f g hf hg (_, SimplexCategory.toTopHomeo _ _)
    rw [Path.Homotopy.target, Path.Homotopy.target]
  rw [he, weakObjectCompositionCube_one, weakObjectSquare_terminal]

/-- The original triangle compares the two original weak-square paths with their composite. -/
def weakObjectSquareCompositionTrack :
    ((W.weakObjectSquareLoopPath f hf).trans (W.weakObjectSquareLoopPath g hg)).Homotopy
      (W.weakObjectSquareLoopPath (f ≫ g) (W.weq.comp_mem _ _ hf hg)) where
  toFun z := W.weakObjectCompositionLoops f g hf hg z
  continuous_toFun := (W.weakObjectCompositionLoops f g hf hg).continuous
  map_zero_left s := by
    apply Path.ext
    funext t
    change W.weakObjectCompositionCube f g hf hg (0, s, t) =
      ((W.weakObjectSquareLoopPath f hf).trans (W.weakObjectSquareLoopPath g hg) s) t
    rw [weakObjectCompositionCube_zero, Path.trans_apply]
    split_ifs <;> rfl
  map_one_left s := by
    apply Path.ext
    funext t
    exact W.weakObjectCompositionCube_one f g hf hg s t
  prop' r s hs := by
    rcases hs with hs | hs
    · subst s
      apply Path.ext
      funext t
      change W.weakObjectCompositionCube f g hf hg (r, 0, t) = _
      rw [weakObjectCompositionCube_nerve_zero]
      exact congrArg (fun p ↦ p t)
        ((W.weakObjectSquareLoopPath f hf).trans (W.weakObjectSquareLoopPath g hg)).source.symm
    · rw [Set.mem_singleton_iff] at hs
      subst s
      apply Path.ext
      funext t
      change W.weakObjectCompositionCube f g hf hg (r, 1, t) = _
      rw [weakObjectCompositionCube_nerve_one]
      exact congrArg (fun p ↦ p t)
        ((W.weakObjectSquareLoopPath f hf).trans (W.weakObjectSquareLoopPath g hg)).target.symm

/-- All three original coordinates remain unchanged by the loop-space comparison. -/
theorem weakObjectSquareCompositionTrack_apply (r s t : unitInterval) :
    W.weakObjectSquareCompositionTrack f g hf hg (r, s) t =
      W.weakObjectCompositionCube f g hf hg (r, s, t) := rfl

end Quillen.Waldhausen.Structure
