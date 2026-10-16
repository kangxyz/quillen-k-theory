/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.SelfTrackStableNaturality

/-! # The original source and target maps on the integer-graded self-track operation -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory Quillen Quillen.LoopPrespectrum
universe u
namespace QuillenTest.SelfTrackStableNaturality

/-- The original target map is retained in every integer degree. -/
theorem original_target_map {E F G : LoopPrespectrum.{u}} {f : E ⟶ F}
    (H : Homotopy f f) (j : F ⟶ G) (d : ℤ) :
    (H.postcomp j).stableOperation d =
      H.stableOperation d ≫ (stableHomotopyFunctor (d + 1)).map j :=
  H.stableOperation_postcomp j d

/-- The original source map is retained in every integer degree. -/
theorem original_source_map {D E F : LoopPrespectrum.{u}} {f : E ⟶ F}
    (H : Homotopy f f) (i : D ⟶ E) (d : ℤ) :
    (H.precomp i).stableOperation d = (stableHomotopyFunctor d).map i ≫ H.stableOperation d :=
  H.stableOperation_precomp i d

end QuillenTest.SelfTrackStableNaturality
