/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyGroups.GenLoopSelfTrackKOne

/-! Original path coordinates and the genuine inversion between the two normalizations. -/
@[expose] public section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
open Quillen
open scoped Topology unitInterval
universe u
namespace QuillenTest.GenLoopSelfTrackKOne
variable {X : Type u} [TopologicalSpace X] {x : X}

/-- The converted original self-track keeps both actual parameters. -/
theorem original_track_coordinates (γ : Path x x) (α : Path γ γ)
    (t s : unitInterval) :
    (α.map (genLoopHomeomorphOfUnique (Fin 1)).symm.continuous) t (fun _ => s) =
      α t s := rfl

/-- The two original classes cancel in the original second homotopy group. -/
theorem original_normalizations_cancel (γ : Path x x) (α : Path γ γ) :
    genLoopSelfTrackClass 0 ((genLoopHomeomorphOfUnique (Fin 1)).symm γ)
        (α.map (genLoopHomeomorphOfUnique (Fin 1)).symm.continuous) *
      loopKOneNormalization γ ⟦α⟧ = 1 := by
  rw [genLoopSelfTrackClass_finOne_eq_inv, inv_mul_cancel]

/-- The actual transposed normalized cube has the inverse original class. -/
theorem original_transposed_cube_class (γ : Path x x) (α : Path γ γ) :
    (⟦transposeGenLoop (0 : Fin 2) 1 Fin.zero_ne_one
      (loopUncurry ((genLoopHomeomorphOfUnique (Fin 1)).symm
        (loopNormalizedSelfTrack γ α)))⟧ : HomotopyGroup.Pi 2 X x) =
      (loopKOneNormalization γ ⟦α⟧)⁻¹ := by
  exact (transposeGenLoop_class (0 : Fin 2) 1 Fin.zero_ne_one _).trans
    (congrArg (fun a : HomotopyGroup.Pi 2 X x => a⁻¹)
      (loopNormalizedSelfTrack_finOne_cube_class γ α))

end QuillenTest.GenLoopSelfTrackKOne
