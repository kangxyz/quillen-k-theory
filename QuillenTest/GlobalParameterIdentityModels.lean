/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalParameterIdentityModels

/-! # Actual integer-base projection, support, and full-open endpoint regression -/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Products
open Quillen.PerfectComplexes.GlobalSectionChangeIndex
open ParameterIdentity
universe u
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

example : (projectionIso Q).hom = pullback.snd _ _ := projectionIso_hom Q

example : (supportedIso f).hom ≫ (ParameterModels.forget f).app (op integerBase) =
    supportedForget (X := op Q) f ≫ (ambientIso Q).hom := supportedIso_forget f

example : (ambientIso Q).hom ≫
      ((ParameterModels.changeWeak f).app (op integerBase) ≫
        (ParameterModels.openRestriction f).app (op integerBase)) =
    globalModel.map f.op ≫ (ambientIso P).hom := ambientIso_fullRestriction f
