/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.Plus.StableProjectiveLocalHomology
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Matrix.Basic

/-! # Original stable completion with arbitrary target local systems -/

@[expose] public section

open CategoryTheory Quillen Quillen.FiniteProjectiveModule

universe u

example (R : Type u) [Ring R]
    (A : LocalCoefficients.System.{u + 1, u + 1} (StableCompletion.ZeroComponent R)) :
    QuasiIso (LocalCoefficients.UniverseLift.chainMap.{u, u + 1, u + 1}
      (StableCompletion.stableZeroMap R) A) :=
  StableFreeRight.stableZeroMap_localCoefficients_quasiIso R A

example (A : LocalCoefficients.System (StableCompletion.ZeroComponent (ZMod 1))) (n : ℕ) :
    IsIso (LocalCoefficients.UniverseLift.homologyMap.{0, 1, 1}
      (StableCompletion.stableZeroMap (ZMod 1)) A n) :=
  StableFreeRight.stableZeroMap_localHomology_isIso (ZMod 1) A n

example (A : LocalCoefficients.System
    (StableCompletion.ZeroComponent (Matrix (Fin 2) (Fin 2) ℤ))) :
    QuasiIso (LocalCoefficients.UniverseLift.chainMap.{0, 1, 1}
      (StableCompletion.stableZeroMap (Matrix (Fin 2) (Fin 2) ℤ)) A) :=
  StableFreeRight.stableZeroMap_localCoefficients_quasiIso (Matrix (Fin 2) (Fin 2) ℤ) A
