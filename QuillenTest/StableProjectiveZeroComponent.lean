/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Quillen.KTheory.Plus.StableProjectiveZeroComponent
import Mathlib.Data.ZMod.Basic
/-! Consumers of the actual matrix comparison, including the zero ring. -/
noncomputable section
open CategoryTheory Quillen Quillen.FiniteProjectiveModule
universe u
example (R : Type u) [Ring R] :
    ContinuousMap.HomotopyEquiv
      (ClassifyingSpace (StableGeneralLinear.GrothendieckModel.Telescope R))
      (pathComponent (classifyingSpacePoint (projectiveTelescopeBase R))) :=
  StableFreeRight.matrixTelescopeZeroComponentHomotopyEquiv R
example :
    ContinuousMap.HomotopyEquiv
      (ClassifyingSpace (StableGeneralLinear.GrothendieckModel.Telescope (ZMod 1)))
      (pathComponent (classifyingSpacePoint (projectiveTelescopeBase (ZMod 1)))) :=
  StableFreeRight.matrixTelescopeZeroComponentHomotopyEquiv (ZMod 1)
example (R : Type u) [Ring R]
    (x : ClassifyingSpace (StableGeneralLinear.GrothendieckModel.Telescope R)) :
    (StableFreeRight.matrixTelescopeZeroComponentHomotopyEquiv R x).val =
      classifyingSpaceMapUniversal (StableFreeRight.telescopeFunctor R) x :=
  StableFreeRight.matrixTelescopeZeroComponentHomotopyEquiv_val R x
