/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedProductUnitInterchange

/-! # External use of the original supported global-unit normalization -/
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.PerfectComplexes
open Quillen.Waldhausen.IteratedS
open Quillen.PerfectComplexes.SupportedGlobalUnitIdentityOperation
universe u

/-- The original supported track, with its rebased endpoint, keeps every scalar-action time. -/
example {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (r : (Γ(X, ⊤))ˣ)
    (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectSupportedWaldhausen j)).space n) :
    (boundedFlatPerfectSupportedGlobalUnitHomotopy j r).level n (t, x) =
      (prespectrumIsoHomotopy (𝟙 (modelOf (boundedFlatPerfectSupportedWaldhausen j)))
        (SupportedTensorEvaluation.smallUnit (X := Opposite.op X) j r)).level n
        (t, (boundedFlatPerfectSupportedIdentityPrespectrumMap j).map n x) :=
  congrArg (fun H ↦ H (t, x)) (originalUnit_level j r n)
