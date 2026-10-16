/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.SelfTrackStableNullEvaluation

/-! # Original null-loop and original mapping-cone transition in every integer degree -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory Quillen Quillen.LoopPrespectrum
universe u
namespace QuillenTest.SelfTrackStableNullEvaluation

/-- The same supplied original nullhomotopy occurs in the actual map being evaluated. -/
theorem original_null_map {E F : LoopPrespectrum.{u}} {f : E ⟶ F}
    (H : Homotopy f f) (N : Homotopy f (zeroHom E F)) (d : ℤ) :
    (stableHomotopyFunctor d).map (H.nullLoopMap N) ≫ (parameterStableHomotopyIso F d).hom =
      H.stableOperation d :=
  H.nullLoopMap_stableHomotopy N d

/-- The existing original cone transition factors through its existing original inclusion. -/
theorem original_cone_transition {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    (H : Homotopy f f) (d : ℤ) :
    (stableHomotopyFunctor d).map (mappingConeLoopTransition f H) ≫
        (parameterStableHomotopyIso (mappingCone f) d).hom =
      H.stableOperation d ≫ (stableHomotopyFunctor (d + 1)).map (mappingConeInclusion f) :=
  mappingConeLoopTransition_stableHomotopy f H d

end QuillenTest.SelfTrackStableNullEvaluation
