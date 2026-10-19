/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputIdentityCharts

/-! A separate client of the literal global raw span identity and unchanged chart times. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalRawBass
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace Consumer.GlobalRawBassInputIdentity

/-- The original whole span contracts to identity while its positive chart keeps the full unit. -/
theorem whole_span_with_original_chart (X : Scheme.{u}) :
    ∃ H : Homotopy (spanMap (𝟙 X)) (𝟙 (span X)),
      ∀ (n : ℕ) (r : unitInterval)
        (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (polynomial.obj X))).space n),
        H.level n
          (r, (HomotopyPushout.inl (boundedFlatPerfectPrespectrumMap (projection.app X))
            (boundedFlatPerfectPrespectrumMap (projection.app X))).map n x) =
          (HomotopyPushout.inl (boundedFlatPerfectPrespectrumMap (projection.app X))
            (boundedFlatPerfectPrespectrumMap (projection.app X))).map n
              ((boundedFlatPerfectPrespectrumIdHomotopy (polynomial.obj X)).level n (r, x)) :=
  ⟨InputIdentity.spanHomotopy X, InputIdentity.spanHomotopy_inl X⟩

end Consumer.GlobalRawBassInputIdentity
