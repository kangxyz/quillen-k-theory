/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.SelfTrackPath

/-! # Literal original path coordinates and finite degree-one normalization consumers -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory Quillen Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace QuillenTest.SelfTrackPath
variable {E F : LoopPrespectrum.{u}} {f : E ⟶ F}

/-- Track and spatial times remain the two original arguments, including spectrum level zero. -/
theorem original_level_zero_coordinates (H : Homotopy f f)
    (γ : Path (E.point 0) (E.point 0)) (t s : unitInterval) :
    H.pathSelfTrack 0 γ t s = H.level 0 (t, γ s) := rfl

/-- The actual cube track, with its corrected endpoint, has the same original path image. -/
theorem original_path_image (H : Homotopy f f) (n : ℕ)
    (γ : Path (E.point n) (E.point n)) :
    (H.genLoopPath n ((genLoopHomeomorphOfUnique (Fin 1)).symm γ)).map
        (genLoopHomeomorphOfUnique (Fin 1)).continuous = H.pathSelfTrack n γ :=
  H.genLoopPath_finOne_map n γ

/-- Finite degree one retains the exact original path normalization and its single inverse. -/
theorem original_degree_one_normalization (H : Homotopy f f) (n : ℕ)
    (γ : Path (E.point n) (E.point n)) :
    H.homotopyClassOperation n 0
        ⟦(genLoopHomeomorphOfUnique (Fin 1)).symm γ⟧ =
      (loopKOneNormalization (basedLoopMap (f.map n) (f.map_point n) γ)
        ⟦H.pathSelfTrack n γ⟧)⁻¹ :=
  H.homotopyClassOperation_finOne n γ

end QuillenTest.SelfTrackPath
