/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorNormalizedRowPresentation

/-! # Actual normalized ambient and supported comparison maps in all signed degrees -/
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.LoopPrespectrum Quillen.PerfectComplexes
open ParameterTensorNormalizedRowPresentation
universe u

example (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) (d : ℤ) :
    IsIso ((stableHomotopyFunctor d).map (ambientComparison Q X)) :=
  ambientComparison_stable Q X d

example {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]
    (X : Scheme.{u}ᵒᵖ) (d : ℤ) :
    IsIso ((stableHomotopyFunctor d).map (supportedComparison f X)) :=
  supportedComparison_stable f X d
