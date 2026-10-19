/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedParameterDoubleUnit

/-! # The original supported double-unit sign retains a supplied target comparison -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalSectionChangeIndex
open Quillen.PerfectComplexes.SupportedParameterDoubleUnit
universe u

example {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (X : Scheme.{u}ᵒᵖ)
    (Z : Quillen.LoopPrespectrum.{u + 1})
    (k : prespectrum ((ParameterModels.supported f).obj (laurent.op.obj (laurent.op.obj X))) ⟶ Z) :
    doubleUnit f X ≫ (stableHomotopyFunctor 2).map
      (prespectrumMap ((ParameterModels.supported f).map
        (baseProductSwapMap (laurentProjection (.of (ULift.{u} ℤ)))
          (laurentProjection (.of (ULift.{u} ℤ))) X.unop).op)) ≫
      (stableHomotopyFunctor 2).map k =
    -(doubleUnit f X ≫ (stableHomotopyFunctor 2).map k) := by
  have h := congrArg (fun t => t ≫ (stableHomotopyFunctor 2).map k)
    (doubleUnit_swap f X)
  exact (Category.assoc _ _ _).symm.trans (h.trans (Preadditive.neg_comp _ _))
