/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC1SeedFaceNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassNegativeMixedRoutes

/-! The inverse outer chart retains the genuine seed, forward inner unit, and fixed pause. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassNegativeC1CarrierSeedNative
open CoefficientBassPositiveC1SeedFaceNative CoefficientBassPositiveC1SeedFace
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (d : Under R)

/-- The original source cast changes no comparison or inner loop coordinate. -/
theorem face_supported (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, d)))).space n) :
    evaluate P ((polynomialUnderCoefficient R).app d) ((underToLaurentInvert R).app d) n
      (face P ((polynomialUnderCoefficient R).app d) ((underToLaurentInvert R).app d) (r, s)) x =
      Path.toContinuousMap
        ((CoefficientBassNegativeMixedRoutes.supportedComposition P d).level n
          (r, (boundedFlatCoefficientBassPositiveConeSeed P d).map n x)) s := by
  dsimp only [CoefficientBassNegativeMixedRoutes.supportedComposition, Homotopy.cast]
  exact face_native P ((polynomialUnderCoefficient R).app d)
    ((underToLaurentInvert R).app d) n r s x

/-- The entire negative C1 image is the original SecondMinus homotopy on the genuine seed. -/
theorem face_original (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, d)))).space n) :
    (boundedFlatCoefficientBassPositiveConeInclusion P ((laurentUnderFunctor R).obj d)).map n
      (evaluate P ((polynomialUnderCoefficient R).app d) ((underToLaurentInvert R).app d) n
        (face P ((polynomialUnderCoefficient R).app d)
          ((underToLaurentInvert R).app d) (r, s)) x) =
      Path.toContinuousMap ((boundedFlatCoefficientBassSecondMinusHomotopy P d).level n
        (r, (boundedFlatCoefficientBassTransition P d).map n x)) s := by
  have h := CoefficientBassPositiveCompositionTrack.stepComposition_seed P
    ((polynomialUnderCoefficient R).app d) ((underToLaurentInvert R).app d) n r s x
  rw [face_supported]
  dsimp only [CoefficientBassNegativeMixedRoutes.supportedComposition,
    boundedFlatCoefficientBassSecondMinusHomotopy, Homotopy.cast]
  exact h

end Quillen.PerfectComplexes.CoefficientBassNegativeC1CarrierSeedNative
