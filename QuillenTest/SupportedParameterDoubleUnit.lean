/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedParameterDoubleUnit

/-! # The supported double-unit sign on the unchanged original stable class -/
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalSectionChangeIndex
universe u

example {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (X : Scheme.{u}ᵒᵖ)
    (a : stableHomotopyGroup (prespectrum ((ParameterModels.supported f).obj X)) 0) :
    (stableHomotopyFunctor 2).map
      (prespectrumMap ((ParameterModels.supported f).map
        (baseProductSwapMap (laurentProjection (.of (ULift.{u} ℤ)))
          (laurentProjection (.of (ULift.{u} ℤ))) X.unop).op))
      (((ParameterLaurentTrack.supportedTrack f).homotopy (laurent.op.obj X)).stableOperation 1
        (((ParameterLaurentTrack.supportedTrack f).homotopy X).stableOperation 0 a)) =
      -(((ParameterLaurentTrack.supportedTrack f).homotopy (laurent.op.obj X)).stableOperation 1
        (((ParameterLaurentTrack.supportedTrack f).homotopy X).stableOperation 0 a)) :=
  ConcreteCategory.congr_hom (SupportedParameterDoubleUnit.doubleUnit_swap f X) a
