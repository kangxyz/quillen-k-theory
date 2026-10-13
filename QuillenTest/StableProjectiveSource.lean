/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Quillen.KTheory.Plus.StableProjectiveSource
/-! The original stable group and original inverse-homotopy basepoint track. -/
noncomputable section
open Quillen Quillen.FiniteProjectiveModule CategoryTheory
universe u
example (R : Type u) [Ring R] :
    ContinuousMap.HomotopyEquiv
      (ClassifyingSpace (SingleObj (StableGeneralLinear.Group R)))
      (pathComponent (classifyingSpacePoint (projectiveTelescopeBase R))) :=
  StableFreeRight.stableProjectiveZeroHomotopyEquiv R
example (R : Type u) [Ring R]
    (x : ClassifyingSpace (SingleObj (StableGeneralLinear.Group R))) :
    (StableFreeRight.stableProjectiveZeroHomotopyEquiv R x).val =
      classifyingSpaceMapUniversal (StableFreeRight.telescopeFunctor R)
        (StableCompletion.originalStableToTelescope R x) :=
  StableFreeRight.stableProjectiveZeroHomotopyEquiv_val R x
example (R : Type u) [Ring R] :
    Path (StableFreeRight.stableProjectiveZeroHomotopyEquiv R (StableCompletion.stableBase R))
      (⟨classifyingSpacePoint (projectiveTelescopeBase R), Joined.refl _⟩ :
        pathComponent (classifyingSpacePoint (projectiveTelescopeBase R))) :=
  StableFreeRight.stableProjectiveZeroBasepointPath R
