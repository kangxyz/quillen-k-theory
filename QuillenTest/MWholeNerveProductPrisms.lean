/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveProductPrisms

/-! The four actual ninety-node prisms retain every native coordinate and original input. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option linter.mathlibStandardSet true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen Quillen.PerfectComplexes Quillen.PerfectComplexes.BassMWholeNerve
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace QuillenTest.MWholeNerveProductPrisms
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (u : a ⟶ b) (v : b ⟶ c) (w : c ⟶ d)

/-- The entire positive polynomial product retains its original native evaluation. -/
theorem positive_polynomial_family (n : ℕ) (q s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily _
      (polynomialProductPrism P u v w (underToLaurent R) (laurentPlus_projection P c) false) n
      (![q, s, t], x) =
    (CoefficientTransformationComposition.square P (underToLaurent R) w).level n
      (s, (CoefficientTransformationComposition.movingSquare P (polynomialUnderCoefficient R)
        u v).level n (q, (t, x))) :=
  polynomial_product_compact_native P u v w (underToLaurent R) (laurentPlus_projection P c) false
    n q s t x

/-- All original level-zero inputs retain the full positive polynomial product. -/
theorem positive_polynomial_zero (q s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space 0) :
    CommonReferenceNerve.compactPrespectrumFamily _
      (polynomialProductPrism P u v w (underToLaurent R) (laurentPlus_projection P c) false) 0
      (![q, s, t], x) =
    (CoefficientTransformationComposition.square P (underToLaurent R) w).level 0
      (s, (CoefficientTransformationComposition.movingSquare P (polynomialUnderCoefficient R)
        u v).level 0 (q, (t, x))) :=
  positive_polynomial_family P u v w 0 q s t x

/-- The entire positive chart product retains its original native evaluation. -/
theorem positive_chart_family (n : ℕ) (q s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily _
      (chartProductPrism P u v w (underToLaurent R) (laurentPlus_projection P d) false) n
      (![q, s, t], x) =
    (CoefficientTransformationComposition.movingSquare P (underToLaurent R) v w).level n
      (q, (s, (boundedFlatCoefficientPolynomialSquareHomotopy P u).level n (t, x))) :=
  chart_product_compact_native P u v w (underToLaurent R) (laurentPlus_projection P d) false
    n q s t x

/-- All original level-zero inputs retain the full positive chart product. -/
theorem positive_chart_zero (q s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space 0) :
    CommonReferenceNerve.compactPrespectrumFamily _
      (chartProductPrism P u v w (underToLaurent R) (laurentPlus_projection P d) false) 0
      (![q, s, t], x) =
    (CoefficientTransformationComposition.movingSquare P (underToLaurent R) v w).level 0
      (q, (s, (boundedFlatCoefficientPolynomialSquareHomotopy P u).level 0 (t, x))) :=
  positive_chart_family P u v w 0 q s t x

/-- The entire inverse polynomial product retains its original native evaluation. -/
theorem inverse_polynomial_family (n : ℕ) (q s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily _
      (polynomialProductPrism P u v w (underToLaurentInvert R) (laurentMinus_projection P c) true) n
      (![q, s, t], x) =
    (CoefficientTransformationComposition.square P (underToLaurentInvert R) w).level n
      (s, (CoefficientTransformationComposition.movingSquare P (polynomialUnderCoefficient R)
        u v).level n (q, (unitInterval.symm t, x))) :=
  polynomial_product_compact_native P u v w (underToLaurentInvert R)
    (laurentMinus_projection P c) true
    n q s t x

/-- All original level-zero inputs retain the full inverse polynomial product. -/
theorem inverse_polynomial_zero (q s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space 0) :
    CommonReferenceNerve.compactPrespectrumFamily _
      (polynomialProductPrism P u v w (underToLaurentInvert R) (laurentMinus_projection P c) true) 0
      (![q, s, t], x) =
    (CoefficientTransformationComposition.square P (underToLaurentInvert R) w).level 0
      (s, (CoefficientTransformationComposition.movingSquare P (polynomialUnderCoefficient R)
        u v).level 0 (q, (unitInterval.symm t, x))) :=
  inverse_polynomial_family P u v w 0 q s t x

/-- The entire inverse chart product retains its original native evaluation. -/
theorem inverse_chart_family (n : ℕ) (q s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily _
      (chartProductPrism P u v w (underToLaurentInvert R) (laurentMinus_projection P d) true) n
      (![q, s, t], x) =
    (CoefficientTransformationComposition.movingSquare P (underToLaurentInvert R) v w).level n
      (q, (s, (boundedFlatCoefficientPolynomialSquareHomotopy P u).level n
        (unitInterval.symm t, x))) :=
  chart_product_compact_native P u v w (underToLaurentInvert R) (laurentMinus_projection P d) true
    n q s t x

/-- All original level-zero inputs retain the full inverse chart product. -/
theorem inverse_chart_zero (q s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space 0) :
    CommonReferenceNerve.compactPrespectrumFamily _
      (chartProductPrism P u v w (underToLaurentInvert R) (laurentMinus_projection P d) true) 0
      (![q, s, t], x) =
    (CoefficientTransformationComposition.movingSquare P (underToLaurentInvert R) v w).level 0
      (q, (s, (boundedFlatCoefficientPolynomialSquareHomotopy P u).level 0
        (unitInterval.symm t, x))) :=
  inverse_chart_family P u v w 0 q s t x

variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)

/-- The polynomial product keeps structure time independent of all three scalar coordinates. -/
theorem polynomial_independent_structure
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (inverse : Bool) (n : ℕ) (q s t h : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily _
      (polynomialProductPrism P u v w α hc inverse) (n + 1)
      (![q, s, t], (originalPrespectrum
        (boundedFlatPerfectWaldhausen (space (op P, a)))).structureMap n x h) =
      (originalPrespectrum (boundedFlatPerfectWaldhausen
        (space (op P, (laurentUnderFunctor R).obj d)))).structureMap n
          (CommonReferenceNerve.compactPrespectrumFamily _
      (polynomialProductPrism P u v w α hc inverse) n
            (![q, s, t], x)) h :=
  CommonReferenceNerve.compactPrespectrumFamily_structure _
      (polynomialProductPrism P u v w α hc inverse) n
    ![q, s, t] x h

/-- The entire polynomial product preserves the original level-zero based line. -/
theorem polynomial_based_zero
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (inverse : Bool) (q s t : unitInterval) :
    CommonReferenceNerve.compactPrespectrumFamily _ (polynomialProductPrism P u v w α hc inverse) 0
      (![q, s, t], (originalPrespectrum
        (boundedFlatPerfectWaldhausen (space (op P, a)))).point 0) =
      (originalPrespectrum (boundedFlatPerfectWaldhausen
        (space (op P, (laurentUnderFunctor R).obj d)))).point 0 :=
  CommonReferenceNerve.compactPrespectrumFamily_point _
      (polynomialProductPrism P u v w α hc inverse) 0
    ![q, s, t]

/-- The polynomial product also retains the original input loop's independent time. -/
theorem polynomial_independent_input_loop
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (inverse : Bool) (q s t h : unitInterval)
    (γ : Path (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (space (op P, a)))))
      (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (space (op P, a)))))) :
    (show Path
      (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen
        (space (op P, (laurentUnderFunctor R).obj d)))))
      (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen
        (space (op P, (laurentUnderFunctor R).obj d))))) from
      CommonReferenceNerve.compactPrespectrumFamily _
      (polynomialProductPrism P u v w α hc inverse) 0
        (![q, s, t], γ)) h =
      CommonReferenceNerve.compactStageFamily _ 0 (polynomialProductPrism P u v w α hc inverse)
        (![q, s, t], γ h) :=
  CommonReferenceNerve.compactPrespectrumFamily_zero_apply _
      (polynomialProductPrism P u v w α hc inverse)
    ![q, s, t] γ h

/-- The chart product keeps structure time independent of all three scalar coordinates. -/
theorem chart_independent_structure
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool) (n : ℕ) (q s t h : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily _ (chartProductPrism P u v w α hd inverse) (n + 1)
      (![q, s, t], (originalPrespectrum
        (boundedFlatPerfectWaldhausen (space (op P, a)))).structureMap n x h) =
      (originalPrespectrum (boundedFlatPerfectWaldhausen
        (space (op P, (laurentUnderFunctor R).obj d)))).structureMap n
          (CommonReferenceNerve.compactPrespectrumFamily _
      (chartProductPrism P u v w α hd inverse) n
            (![q, s, t], x)) h :=
  CommonReferenceNerve.compactPrespectrumFamily_structure _
      (chartProductPrism P u v w α hd inverse) n
    ![q, s, t] x h

/-- The entire chart product preserves the original level-zero based line. -/
theorem chart_based_zero
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool) (q s t : unitInterval) :
    CommonReferenceNerve.compactPrespectrumFamily _ (chartProductPrism P u v w α hd inverse) 0
      (![q, s, t], (originalPrespectrum
        (boundedFlatPerfectWaldhausen (space (op P, a)))).point 0) =
      (originalPrespectrum (boundedFlatPerfectWaldhausen
        (space (op P, (laurentUnderFunctor R).obj d)))).point 0 :=
  CommonReferenceNerve.compactPrespectrumFamily_point _ (chartProductPrism P u v w α hd inverse) 0
    ![q, s, t]

/-- The chart product also retains the original input loop's independent time. -/
theorem chart_independent_input_loop
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool) (q s t h : unitInterval)
    (γ : Path (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (space (op P, a)))))
      (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen (space (op P, a)))))) :
    (show Path
      (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen
        (space (op P, (laurentUnderFunctor R).obj d)))))
      (stagePoint 0 (modelOf (boundedFlatPerfectWaldhausen
        (space (op P, (laurentUnderFunctor R).obj d))))) from
      CommonReferenceNerve.compactPrespectrumFamily _ (chartProductPrism P u v w α hd inverse) 0
        (![q, s, t], γ)) h =
      CommonReferenceNerve.compactStageFamily _ 0 (chartProductPrism P u v w α hd inverse)
        (![q, s, t], γ h) :=
  CommonReferenceNerve.compactPrespectrumFamily_zero_apply _
      (chartProductPrism P u v w α hd inverse)
    ![q, s, t] γ h

end QuillenTest.MWholeNerveProductPrisms
