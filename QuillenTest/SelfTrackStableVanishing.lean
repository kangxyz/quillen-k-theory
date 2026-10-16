/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.SelfTrackStableVanishing

/-! # Original stable vanishing without additional topological hypotheses -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory Quillen Quillen.LoopPrespectrum
universe u
namespace QuillenTest.SelfTrackStableVanishing

/-- Only the original intermediate one-higher stable group is required to vanish. -/
theorem original_null_map_all_degrees {E F G : LoopPrespectrum.{u}} {f : E ⟶ F}
    (H : Homotopy f f) (j : F ⟶ G) (N : Homotopy (f ≫ j) (zeroHom E G))
    (d : ℤ) (hF : Subsingleton (stableHomotopyGroup F (d + 1))) :
    (stableHomotopyFunctor d).map ((H.postcomp j).nullLoopMap N) = 0 :=
  H.nullLoopMap_stableMap_zero_of_stable j N d hF

/-- Negative degree uses the same original cone transition and original stable degree zero. -/
theorem original_cone_negative_one {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    (H : Homotopy f f) (hF : Subsingleton (stableHomotopyGroup F 0)) :
    (stableHomotopyFunctor (-1)).map (mappingConeLoopTransition f H) = 0 := by
  exact mappingConeLoopTransition_stableMap_zero_of_stable f H (-1) (by simpa using hF)

end QuillenTest.SelfTrackStableVanishing
