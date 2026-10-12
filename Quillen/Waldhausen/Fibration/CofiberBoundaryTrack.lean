/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.Fibration.CofiberPrismBoundary
public import Quillen.Waldhausen.GrothendieckComparison.WeakObjectCompositionTrack

/-!
# Exact endpoint paths in the original cofiber-prism boundary

The original prism boundary is expressed using its actual object-loop endpoints, the specified
identity-cofiber suffix, and the original inclusion square. Its forward quotient prefix is
retained pointwise so the later canonical-fiber reversal has a fixed orientation.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits unitInterval
open scoped Topology
universe u v
namespace Quillen.Waldhausen.Structure
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  (W : Structure C) {A B Q : C} (i : A ⟶ B) (q : B ⟶ Q)
  (hi : W.cof i) (hwi : W.weq i)
  (hQ : IsPushout i (0 : A ⟶ W.zero) q (0 : W.zero ⟶ Q))

/-- Curry the actual cofiber triangle into its prescribed path of original based loops. -/
def cofiberObjectLoopPath :
    Path ((W.kZeroObjectLoop A).trans (W.kZeroObjectLoop Q)) (W.kZeroObjectLoop B) where
  toFun s := (W.cofiberObjectLoopTrack i q hi hQ).eval s
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    exact (W.cofiberObjectLoopTrack i q hi hQ).continuous
  source' := Path.Homotopy.eval_zero _
  target' := Path.Homotopy.eval_one _

/-- The actual forward zero-to-quotient prefix is the original comparison-zero prism edge. -/
def cofiberPrismPrefixLoopPath :
    Path ((W.kZeroObjectLoop A).trans (Path.refl W.kBasepoint))
      ((W.kZeroObjectLoop A).trans (W.kZeroObjectLoop Q)) where
  toFun s := W.cofiberPrismCompositionLoops i q hi hwi hQ (0, s)
  continuous_toFun := (W.cofiberPrismCompositionLoops i q hi hwi hQ).continuous.comp
    (continuous_const.prodMk continuous_id)
  source' := by
    apply Path.ext
    funext t
    change W.cofiberPrismCompositionCube i q hi hwi hQ (0, 0, t) = _
    rw [cofiberPrismCompositionCube_nerve_zero, ContinuousMap.HomotopyWith.apply_zero]
    change ((W.kZeroObjectLoop A).trans (W.kZeroObjectLoop W.zero)) t = _
    rw [W.kZeroObjectLoop_zero]
  target' := by
    apply Path.ext
    funext t
    change W.cofiberPrismCompositionCube i q hi hwi hQ (0, 1, t) = _
    rw [cofiberPrismCompositionCube_nerve_one, ContinuousMap.HomotopyWith.apply_zero]
    rfl

/-- The full original boundary comparison with the literal object-loop endpoints. -/
def cofiberBoundaryTrack :
    ((W.cofiberPrismPrefixLoopPath i q hi hwi hQ).trans
      (W.cofiberObjectLoopPath i q hi hQ)).Homotopy
      ((W.identityCofiberSuffixPath A).trans (W.weakObjectSquareLoopPath i hwi)) where
  toFun z := W.cofiberPrismBoundaryHomotopy i q hi hwi hQ z
  continuous_toFun := (W.cofiberPrismBoundaryHomotopy i q hi hwi hQ).continuous
  map_zero_left s := by
    apply Path.ext
    funext t
    change W.cofiberPrismBoundaryHomotopy i q hi hwi hQ (0, s) t =
      ((W.cofiberPrismPrefixLoopPath i q hi hwi hQ).trans
        (W.cofiberObjectLoopPath i q hi hQ) s) t
    rw [cofiberPrismBoundaryHomotopy_zero, Path.trans_apply]
    split_ifs <;> rfl
  map_one_left s := by
    apply Path.ext
    funext t
    change W.cofiberPrismBoundaryHomotopy i q hi hwi hQ (1, s) t =
      ((W.identityCofiberSuffixPath A).trans (W.weakObjectSquareLoopPath i hwi) s) t
    rw [cofiberPrismBoundaryHomotopy_one, Path.trans_apply]
    split_ifs <;> rfl
  prop' r s hs := by
    rcases hs with hs | hs
    · subst s
      change W.cofiberPrismBoundaryHomotopy i q hi hwi hQ (r, 0) = _
      rw [Path.Homotopy.source]
      exact (W.cofiberPrismPrefixLoopPath i q hi hwi hQ).source.trans
        ((W.cofiberPrismPrefixLoopPath i q hi hwi hQ).trans
          (W.cofiberObjectLoopPath i q hi hQ)).source.symm
    · rw [Set.mem_singleton_iff] at hs
      subst s
      change W.cofiberPrismBoundaryHomotopy i q hi hwi hQ (r, 1) = _
      rw [Path.Homotopy.target]
      have ht : W.cofiberPrismCompositionLoops i q hi hwi hQ (1, 1) =
          W.kZeroObjectLoop B := by
        apply Path.ext
        funext t
        change W.cofiberPrismCompositionCube i q hi hwi hQ (1, 1, t) = _
        rw [cofiberPrismCompositionCube_nerve_one, ContinuousMap.HomotopyWith.apply_one]
        rfl
      exact ht.trans ((W.cofiberPrismPrefixLoopPath i q hi hwi hQ).trans
        (W.cofiberObjectLoopPath i q hi hQ)).target.symm

/-- Every original interpolation, boundary and object-loop coordinate is unchanged. -/
theorem cofiberBoundaryTrack_apply (a s t : unitInterval) :
    W.cofiberBoundaryTrack i q hi hwi hQ (a, s) t =
      W.cofiberPrismBoundaryHomotopy i q hi hwi hQ (a, s) t := rfl

end Quillen.Waldhausen.Structure
