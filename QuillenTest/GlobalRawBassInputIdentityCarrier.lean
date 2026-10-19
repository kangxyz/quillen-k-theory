/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputIdentityCarrierSeams

/-! Original levels, whole carrier seams, and independent times of the global identity faces. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalRawBass
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace QuillenTest.GlobalRawBassInputIdentityCarrier
open InputIdentityNodes InputIdentityCarrierCharts InputIdentityCarrierSeams
variable (X : Scheme.{u})

/-- Every original degree-zero input survives the whole initial carrier surface. -/
theorem original_initial_zero (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen X)).space 0) :
    CommonReferenceNerve.compactPrespectrumFamily (source X) (inputFace X) 0 ((s, t), x) =
      (inputDescPasting (𝟙 X)).toSquare.level 0 (s, (t, x)) :=
  (inputFace_native X 0 s t x).trans (inputComparisonHomotopy_cylinder (𝟙 X) 0 s t x)

/-- Both joins hold in the actual common carrier before any prespectrum evaluation. -/
theorem both_carrier_edges (s : unitInterval) :
    inputFace X (s, 0) = chartFace X plus plus_projection (0, s) ∧
      inputFace X (s, 1) = chartFace X minus minus_projection (0, s) :=
  ⟨DFunLike.congr_fun (plus_seam X) s, DFunLike.congr_fun (minus_seam X) s⟩

/-- The inverse carrier preserves a structure time independent of both square coordinates. -/
theorem inverse_independent_structure (n : ℕ) (r s z : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen X)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (source X)
      (chartFace X minus minus_projection) (n + 1)
        ((r, s), (originalPrespectrum (boundedFlatPerfectWaldhausen X)).structureMap n x z) =
      (originalPrespectrum (boundedFlatPerfectWaldhausen (laurent.obj X))).structureMap n
        (CommonReferenceNerve.compactPrespectrumFamily (source X)
          (chartFace X minus minus_projection) n ((r, s), x)) z :=
  CommonReferenceNerve.compactPrespectrumFamily_structure (source X)
    (chartFace X minus minus_projection) n (r, s) x z

/-- The entire positive polynomial-identity edge retains its original unpaused unit time. -/
theorem original_polynomial_time (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen X)).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (source X)
      (chartFace X plus plus_projection) n ((r, 1), x) =
        (boundedFlatPerfectPrespectrumMap (plus.app X)).map n
          ((InputIdentity.polynomialHomotopy X).level n
            (r, (boundedFlatPerfectPrespectrumMap (projection.app X)).map n x)) :=
  (plusFace_native X n r 1 x).trans ((InputIdentity.plusSquare X).right n r _)

end QuillenTest.GlobalRawBassInputIdentityCarrier
