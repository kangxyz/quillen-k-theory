/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialCone
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassNegativeConeSupport

/-! Both genuine polynomial sheets evaluate in the original target Bass cone. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialCone
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b : Under R} (f : a ⟶ b)

/-- The plus sheet retains its literal inclusion into the original target cone. -/
def plusValue (n : ℕ) (z : space P α (underToLaurent R) f)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.space
        (op P, (polynomialUnderFunctor R).obj a)))).space n) :=
  (boundedFlatCoefficientBassPositiveConeInclusion P ((laurentUnderFunctor R).obj b)).map n
    (evaluate P α (underToLaurent R) f n z x)

/-- The plus cylinder preserves outer height and every genuine polynomial input. -/
theorem plusValue_cylinder (n : ℕ) (y : |parameterSSet (polynomialReference P α f)|)
    (t : I) (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.space
        (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    plusValue P α f n (cylinder P α (underToLaurent R) f (y, t)) x =
      ReducedMappingCone.cylinder _ _
        ((boundedFlatCoefficientBassSquareComparison P ((laurentUnderFunctor R).obj b)).map n)
        (t, (HomotopyPushout.inl
          (boundedFlatPerfectPrespectrumMap
            (polynomialProjection P ((laurentUnderFunctor R).obj b)))
          (boundedFlatPerfectPrespectrumMap
            (polynomialProjection P ((laurentUnderFunctor R).obj b)))).map n
            (pointwisePrespectrumFamily (polynomialReference P α f) n y x)) := by
  have h := evaluate_cylinder P α (underToLaurent R) f n y t x
  exact (congrArg
    ((boundedFlatCoefficientBassPositiveConeInclusion P ((laurentUnderFunctor R).obj b)).map n)
    h).trans (boundedFlatCoefficientBassPositiveConeInclusion_cylinder P
      ((laurentUnderFunctor R).obj b) n t
      (pointwisePrespectrumFamily (polynomialReference P α f) n y x))

/-- Every compact plus scalar family has actual joint native continuity. -/
def plusCompactFamily {S : Type u} [TopologicalSpace S] [CompactSpace S]
    (p : C(S, space P α (underToLaurent R) f)) (n : ℕ) :=
  ((boundedFlatCoefficientBassPositiveConeInclusion P ((laurentUnderFunctor R).obj b)).map n).comp
    (compactFamily P α (underToLaurent R) f p n)

/-- The minus sheet retains its literal inclusion into the original target cone. -/
def minusValue (n : ℕ) (z : space P α (underToLaurentInvert R) f)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.space
        (op P, (polynomialUnderFunctor R).obj a)))).space n) :=
  (boundedFlatCoefficientBassNegativeConeInclusion P ((laurentUnderFunctor R).obj b)).map n
    (evaluate P α (underToLaurentInvert R) f n z x)

/-- The minus cylinder preserves outer height and every genuine polynomial input. -/
theorem minusValue_cylinder (n : ℕ) (y : |parameterSSet (polynomialReference P α f)|)
    (t : I) (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.space
        (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    minusValue P α f n (cylinder P α (underToLaurentInvert R) f (y, t)) x =
      ReducedMappingCone.cylinder _ _
        ((boundedFlatCoefficientBassSquareComparison P ((laurentUnderFunctor R).obj b)).map n)
        (t, (HomotopyPushout.inr
          (boundedFlatPerfectPrespectrumMap
            (polynomialProjection P ((laurentUnderFunctor R).obj b)))
          (boundedFlatPerfectPrespectrumMap
            (polynomialProjection P ((laurentUnderFunctor R).obj b)))).map n
            (pointwisePrespectrumFamily (polynomialReference P α f) n y x)) := by
  have h := evaluate_cylinder P α (underToLaurentInvert R) f n y t x
  exact (congrArg
    ((boundedFlatCoefficientBassNegativeConeInclusion P ((laurentUnderFunctor R).obj b)).map n)
    h).trans (boundedFlatCoefficientBassNegativeConeInclusion_cylinder P
      ((laurentUnderFunctor R).obj b) n t
      (pointwisePrespectrumFamily (polynomialReference P α f) n y x))

/-- Every compact minus scalar family has actual joint native continuity. -/
def minusCompactFamily {S : Type u} [TopologicalSpace S] [CompactSpace S]
    (p : C(S, space P α (underToLaurentInvert R) f)) (n : ℕ) :=
  ((boundedFlatCoefficientBassNegativeConeInclusion P ((laurentUnderFunctor R).obj b)).map n).comp
    (compactFamily P α (underToLaurentInvert R) f p n)

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialCone
