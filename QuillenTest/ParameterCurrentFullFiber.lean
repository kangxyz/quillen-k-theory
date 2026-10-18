/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterCurrentFullFiber

/-! # Original current-stage localization: actual projection and all signed degrees -/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Products
open Quillen.LoopPrespectrum
open Quillen.PerfectComplexes.GlobalSectionChangeIndex
open Quillen.PerfectComplexes.ParameterFullCurrentNull
universe u
variable {P Q : Scheme.{u}} (f : P ⟶ Q)
    [IsOpenImmersion f] [CompactSpace P] [CompactSpace Q] [QuasiSeparatedSpace Q]

example : IsStableEquivalence (currentLift f (op integerBase)) :=
  currentLift_integer_isStableEquivalence f

example (d : ℤ) : IsIso ((stableHomotopyFunctor d).map (currentLift f (op integerBase))) :=
  currentLift_integer_signed_isIso f d

example (n : ℕ) :
    IsIso ((stableHomotopyFunctor (-(n : ℤ))).map (currentLift f (op integerBase))) :=
  currentLift_integer_signed_isIso f (-(n : ℤ))

example : (ParameterIdentity.projectionIso Q).hom = pullback.snd _ _ :=
  ParameterIdentity.projectionIso_hom Q

example : (ParameterIdentity.supportedIso f).hom ≫
      (ParameterModels.forget f).app (op integerBase) =
    supportedForget (X := op Q) f ≫ (ParameterIdentity.ambientIso Q).hom :=
  ParameterIdentity.supportedIso_forget f

example : (ParameterIdentity.ambientIso Q).hom ≫
      ((ParameterModels.changeWeak f).app (op integerBase) ≫
        (ParameterModels.openRestriction f).app (op integerBase)) =
    globalModel.map f.op ≫ (ParameterIdentity.ambientIso P).hom :=
  ParameterIdentity.ambientIso_fullRestriction f
