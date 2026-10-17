/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Topology.Prespectrum.RelativeHomotopyTerminalEvaluation
public import Quillen.Topology.Prespectrum.RelativeHomotopyEndpointEvaluation
public import Quillen.Topology.Prespectrum.RelativeHomotopyHorizontal
public import Quillen.Topology.Prespectrum.RelativeHomotopyComposition

/-!
# Literal scalar evaluation of native relative operations

Evaluation fixes only the level and source point. Both comparison and path time remain free.
The original initial-pause equality transport is retained, then evaluated with its actual
whole-track endpoint equalities. No carrier evaluation continuity or native filler is assumed.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Quillen.LoopPrespectrum.Homotopy.RelHomotopy
variable {E F : LoopPrespectrum.{u}} {f g h : E ⟶ F}

/-- Fixing an original point gives the entire scalar relative path homotopy. -/
def path {H K : Homotopy f g} (J : H.RelHomotopy K) (n : ℕ) (x : E.space n) :
    (H.path n x).Homotopy (K.path n x) where
  toFun z := J.level n (z.1, (z.2, x))
  continuous_toFun := by fun_prop
  map_zero_left s := (J.level n).apply_zero (s, x)
  map_one_left s := (J.level n).apply_one (s, x)
  prop' r s hs := by
    apply (J.level n).eq_fst
    rcases hs with hs | hs
    · exact Or.inl hs
    · exact Or.inr (Or.inl hs)

/-- Scalar path evaluation retains the original two independent coordinates literally. -/
theorem path_apply {H K : Homotopy f g} (J : H.RelHomotopy K)
    (n : ℕ) (r s : unitInterval) (x : E.space n) :
    J.path n x (r, s) = J.level n (r, (s, x)) := rfl

/-- The native constant comparison evaluates to the scalar constant comparison. -/
theorem refl_apply_path (H : Homotopy f g)
    (n : ℕ) (r s : unitInterval) (x : E.space n) :
    (refl H).level n (r, (s, x)) = Path.Homotopy.refl (H.path n x) (r, s) := rfl

/-- Reversing comparison time commutes with fixed-point evaluation. -/
theorem symm_apply_path {H K : Homotopy f g} (J : H.RelHomotopy K)
    (n : ℕ) (r s : unitInterval) (x : E.space n) :
    J.symm.level n (r, (s, x)) = (J.path n x).symm (r, s) := rfl

/-- Native comparison concatenation keeps the scalar comparison half cut. -/
theorem trans_apply_path {H K L : Homotopy f g}
    (J : H.RelHomotopy K) (J' : K.RelHomotopy L)
    (n : ℕ) (r s : unitInterval) (x : E.space n) :
    (J.trans J').level n (r, (s, x)) = ((J.path n x).trans (J'.path n x)) (r, s) := by
  change ((J.level n).trans (J'.level n)) (r, (s, x)) = _
  rw [ContinuousMap.HomotopyRel.trans_apply, Path.Homotopy.trans_apply]
  split <;> rfl

/-- Reversing path time commutes with evaluation without reversing comparison time. -/
theorem symmPath_apply_path {H K : Homotopy f g} (J : H.RelHomotopy K)
    (n : ℕ) (r s : unitInterval) (x : E.space n) :
    J.symmPath.level n (r, (s, x)) = (J.path n x).symm₂ (r, s) := rfl

/-- Native horizontal concatenation keeps the literal scalar path-time half cut. -/
theorem hcomp_apply_path {H H' : Homotopy f g} {K K' : Homotopy g h}
    (J : H.RelHomotopy H') (L : K.RelHomotopy K')
    (n : ℕ) (r s : unitInterval) (x : E.space n) :
    (J.hcomp L).level n (r, (s, x)) = ((J.path n x).hcomp (L.path n x)) (r, s) := by
  unfold hcomp
  dsimp only
  change (ContinuousMap.Homotopy.trans (X := unitInterval × E.space n)
    (Y := F.space n) _ _) (s, (r, x)) = _
  rw [ContinuousMap.Homotopy.trans_apply, Path.Homotopy.hcomp_apply]
  split <;> rfl

/-- The original forward-then-reversed contraction has its literal scalar interior. -/
theorem reflTransSymm_apply_path (H : Homotopy f g)
    (n : ℕ) (r s : unitInterval) (x : E.space n) :
    (reflTransSymm H).level n (r, (s, x)) =
      Path.Homotopy.reflTransSymm (H.path n x) (r, s) := rfl

private theorem reflTrans_apply_symm (H : Homotopy f g)
    (n : ℕ) (r s : unitInterval) (x : E.space n) :
    (reflTrans H).level n (r, (s, x)) =
      (transRefl H.symm).symmPath.level n (r, (s, x)) := by
  unfold reflTrans
  apply transport_apply
  all_goals simp only [Homotopy.symm_trans, Homotopy.symm_refl, Homotopy.symm_symm]

/-- Initial-pause cancellation retains the original native transport and scalar clock. -/
theorem reflTrans_apply_path (H : Homotopy f g)
    (n : ℕ) (r s : unitInterval) (x : E.space n) :
    (reflTrans H).level n (r, (s, x)) =
      Path.Homotopy.reflTrans (H.path n x) (r, s) := by
  rw [reflTrans_apply_symm]
  change (transRefl H.symm).level n (r, (unitInterval.symm s, x)) = _
  rw [transRefl_apply_path, Homotopy.path_symm]
  rfl

end Quillen.LoopPrespectrum.Homotopy.RelHomotopy
