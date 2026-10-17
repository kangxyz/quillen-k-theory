/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC0CarrierSeedNative

/-! The inverse outer chart retains the original forward inner seed and fixed composition pause. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.LoopPrespectrum CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.CoefficientBassNegativeC0CarrierSeedNative
open CoefficientBassPositiveC0CarrierSeed CoefficientBassPositiveC0CarrierSeedNative
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (d : Under R)

/-- The inverse coefficient chart changes the outer source leg only, with the original C0 clock. -/
theorem actual_reversed_face_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, d)))).space n) :
    evaluate P ((polynomialUnderCoefficient R).app d) ((underToLaurentInvert R).app d) n
      (reversedFace P ((polynomialUnderCoefficient R).app d)
        ((underToLaurentInvert R).app d) (r, s)) x =
    Path.toContinuousMap
      ((boundedFlatCoefficientBassPositiveConeSeed P ((laurentUnderFunctor R).obj d)).map n
        (((boundedFlatCoefficientLaurentMinusHomotopy P d).symm).level n (r, x))) s :=
  face_native P ((polynomialUnderCoefficient R).app d) ((underToLaurentInvert R).app d)
    n (unitInterval.symm r) s x

/-- The exact reversed native C0 segment of the inverse-chart supported right route. -/
theorem actual_original_C0 (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, d)))).space n) :
    evaluate P ((polynomialUnderCoefficient R).app d) ((underToLaurentInvert R).app d) n
      (reversedFace P ((polynomialUnderCoefficient R).app d)
        ((underToLaurentInvert R).app d) (r, s)) x =
    Path.toContinuousMap
      ((((boundedFlatCoefficientLaurentMinusHomotopy P d).postcomp
        (boundedFlatCoefficientBassPositiveConeSeed P ((laurentUnderFunctor R).obj d))).symm).level
          n (r, x)) s :=
  actual_reversed_face_native P d n r s x

end Quillen.PerfectComplexes.CoefficientBassNegativeC0CarrierSeedNative
