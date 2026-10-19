/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputIdentityCarrierSeams

/-! An independent consumer of the actual identity chart carrier faces and both whole joins. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalRawBass
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace Consumer.GlobalRawBassInputIdentityCarrier
open InputIdentityNodes InputIdentityCarrierCharts InputIdentityCarrierSeams

/-- The two original unit squares share their actual input edges in one full reference carrier. -/
theorem original_chart_faces_and_joins (X : Scheme.{u}) (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen X)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (source X)
        (chartFace X plus plus_projection) n ((r, s), x) =
      (InputIdentity.plusSquare X).level n
        (r, (s, (boundedFlatPerfectPrespectrumMap (projection.app X)).map n x)) ∧
    CommonReferenceNerve.compactPrespectrumFamily (source X)
        (chartFace X minus minus_projection) n ((r, s), x) =
      (InputIdentity.minusSquare X).level n
        (r, (s, (boundedFlatPerfectPrespectrumMap (projection.app X)).map n x)) ∧
    inputFace X (s, 0) = chartFace X plus plus_projection (0, s) ∧
    inputFace X (s, 1) = chartFace X minus minus_projection (0, s) :=
  ⟨plusFace_native X n r s x, minusFace_native X n r s x,
    DFunLike.congr_fun (plus_seam X) s, DFunLike.congr_fun (minus_seam X) s⟩

end Consumer.GlobalRawBassInputIdentityCarrier
