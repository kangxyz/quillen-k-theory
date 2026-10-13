/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.TelescopeContraction

/-!
# Original telescope points and finite-stage basepoint tracks

Every original cylinder point has a displayed path to its original stage point. The finite
prefix contraction also supplies an exact track at every telescope point, and at each original
stage point this ends at the unchanged finite transition into the specified later stage.
The structure-map identity retains both the path time and original loop coordinate.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory
open scoped Topology unitInterval

universe u

namespace Quillen.LoopPrespectrum.Telescope

variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))

/-- The actual cylinder coordinate contracts to its original stage endpoint. -/
def cylinderStagePath (k i : ℕ) (s : unitInterval) (x : (E i).space k) :
    Path (cylinder E f k i (s, x)) ((inclusion E f i).map k x) where
  toFun t := cylinder E f k i (Set.Icc.convexComb s 0 t, x)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp; rfl

/-- Every point is joined to a displayed point of an original stage, with no separation
hypothesis or choice of a path to the chosen basepoint. -/
theorem exists_stage_point (k : ℕ) (y : Space E f k) :
    ∃ i : ℕ, ∃ x : (E i).space k, Nonempty (Path y ((inclusion E f i).map k x)) := by
  induction y using Quot.inductionOn with
  | h z => exact ⟨z.1, z.2.2, ⟨cylinderStagePath E f k z.1 z.2.1 z.2.2⟩⟩

/-- The exact track of a point under the original finite-prefix contraction. -/
def collapsePath (k N : ℕ) (x : Space E f k) :
    Path x ((collapse E f N).map k x) where
  toFun t := (collapseHomotopy E f N).level k (t, x)
  continuous_toFun := ((collapseHomotopy E f N).level k).continuous.comp
    (continuous_id.prodMk continuous_const)
  source' := (collapseHomotopy E f N).at_zero k x
  target' := (collapseHomotopy E f N).at_one k x

/-- The basepoint track commutes with the original structure maps at every independent time
and loop coordinate. -/
theorem collapsePath_structure (k N : ℕ) (x : Space E f k)
    (t r : unitInterval) :
    collapsePath E f (k + 1) N ((prespectrum E f).structureMap k x r) t =
      (prespectrum E f).structureMap k (collapsePath E f k N x t) r :=
  (collapseHomotopy E f N).comm k t x r

/-- The exact original stage point follows the finite-prefix track to its original transition. -/
def stageTransitionPath {i N : ℕ} (hi : i ≤ N) (k : ℕ) (x : (E i).space k) :
    Path ((inclusion E f i).map k x)
      ((inclusion E f N).map k ((transition E f i N hi).map k x)) where
  toFun t := (collapseHomotopy E f N).level k (t, (inclusion E f i).map k x)
  continuous_toFun := ((collapseHomotopy E f N).level k).continuous.comp
    (continuous_id.prodMk continuous_const)
  source' := (collapseHomotopy E f N).at_zero k ((inclusion E f i).map k x)
  target' := ((collapseHomotopy E f N).at_one k ((inclusion E f i).map k x)).trans
    (collapse_inclusion E f hi k x)

/-- The whole stage-transition track is the unchanged contraction evaluated at the original
source point, including all intermediate times. -/
@[simp] theorem stageTransitionPath_apply {i N : ℕ} (hi : i ≤ N) (k : ℕ)
    (x : (E i).space k) (t : unitInterval) :
    stageTransitionPath E f hi k x t =
      (collapseHomotopy E f N).level k (t, (inclusion E f i).map k x) := rfl

/-- The whole original stage track preserves the structure-time coordinate without swapping it
with contraction time. -/
theorem stageTransitionPath_structure {i N : ℕ} (hi : i ≤ N) (k : ℕ)
    (x : (E i).space k) (t r : unitInterval) :
    stageTransitionPath E f hi (k + 1) ((E i).structureMap k x r) t =
      (prespectrum E f).structureMap k (stageTransitionPath E f hi k x t) r := by
  change (collapseHomotopy E f N).level (k + 1)
    (t, (inclusion E f i).map (k + 1) ((E i).structureMap k x r)) = _
  exact (congrArg (fun y ↦ (collapseHomotopy E f N).level (k + 1) (t, y))
    (congrArg (fun γ ↦ γ r) ((inclusion E f i).comm k x))).trans
      ((collapseHomotopy E f N).comm k t ((inclusion E f i).map k x) r)

end Quillen.LoopPrespectrum.Telescope
