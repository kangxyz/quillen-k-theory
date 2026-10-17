/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Topology.Prespectrum.RelativeHomotopyReparam
public import Quillen.Topology.Prespectrum.RelativeHomotopyLevels

/-!
# Exact pointwise terminal-pause evaluation

The original endpoint transport is retained and reduced only after taking its whole level.
Comparison time, path time and the original source point are independent. No carrier evaluator
or actual J0 comparison is assumed.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Quillen.LoopPrespectrum

private theorem transport_level {E F : LoopPrespectrum.{u}} {f g : E ⟶ F}
    {H H' K K' : Homotopy f g} (eH : H = H') (eK : K = K')
    (p : H.RelHomotopy K = H'.RelHomotopy K') (J : H.RelHomotopy K) (n : ℕ) :
    ((p.mp J).level n).toContinuousMap = (J.level n).toContinuousMap := by
  subst H'
  subst K'
  rfl

private def terminalTime : C(unitInterval, unitInterval) :=
  ⟨fun s ↦ ⟨Path.Homotopy.transReflReparamAux s,
    Path.Homotopy.transReflReparamAux_mem_I s⟩, by fun_prop⟩

private theorem terminalTime_zero : terminalTime 0 = 0 :=
  Subtype.ext Path.Homotopy.transReflReparamAux_zero

private theorem terminalTime_one : terminalTime 1 = 1 :=
  Subtype.ext Path.Homotopy.transReflReparamAux_one

private theorem terminal_level {E F : LoopPrespectrum.{u}}
    {f g : E ⟶ F} (H : Homotopy f g) (n : ℕ) :
    ((Homotopy.RelHomotopy.transRefl H).level n).toContinuousMap =
      (((Homotopy.RelHomotopy.reparam H terminalTime
        terminalTime_zero terminalTime_one).symm).level n).toContinuousMap := by
  unfold Homotopy.RelHomotopy.transRefl
  dsimp only
  apply transport_level
  · apply Homotopy.ext
    funext n
    apply ContinuousMap.ext
    rintro ⟨s, x⟩
    have he := Path.Homotopy.trans_refl_reparam (H.path n x)
    rw [← Homotopy.path_refl g n x, ← Homotopy.path_trans] at he
    exact (DFunLike.congr_fun he s).symm
  · rfl

/-- Original terminal-pause cancellation evaluates to the literal path-level cancellation. -/
theorem Homotopy.RelHomotopy.transRefl_apply_path {E F : LoopPrespectrum.{u}}
    {f g : E ⟶ F} (H : Homotopy f g) (n : ℕ) (r s : unitInterval) (x : E.space n) :
    (Homotopy.RelHomotopy.transRefl H).level n (r, (s, x)) =
      Path.Homotopy.transRefl (H.path n x) (r, s) := by
  change ((Homotopy.RelHomotopy.transRefl H).level n).toContinuousMap (r, (s, x)) = _
  rw [terminal_level]
  rfl

/-- Whole-level endpoint casts preserve all comparison and path coordinates literally. -/
theorem Homotopy.RelHomotopy.ofLevels_apply {E F : LoopPrespectrum.{u}}
    {f g f' g' : E ⟶ F} {H K : Homotopy f g}
    (J : H.RelHomotopy K) (H' K' : Homotopy f' g')
    (hH : ∀ n, H'.level n = H.level n) (hK : ∀ n, K'.level n = K.level n)
    (n : ℕ) (r s : unitInterval) (x : E.space n) :
    (J.ofLevels H' K' hH hK).level n (r, (s, x)) = J.level n (r, (s, x)) := rfl

end Quillen.LoopPrespectrum
