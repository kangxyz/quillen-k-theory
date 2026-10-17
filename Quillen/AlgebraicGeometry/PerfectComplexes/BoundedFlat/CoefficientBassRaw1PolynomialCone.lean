/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1LaurentChartRestriction
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCutOpenCompactFamily

/-! The actual single polynomial sheet, with genuine polynomial input and all-level evaluation. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialCone
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (α β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b : Under R} (f : a ⟶ b)

/-- The genuine polynomial-indexed triple has source Polynomial(a). -/
abbrev polynomialReference := NormalizedTripleSimplex.sourceMap
  (coefficientMap P ((polynomialUnderFunctor R).map ((laurentUnderFunctor R).map f)))
  (coefficientMap P ((polynomialUnderFunctor R).map (α.app a)))
  (coefficientMap P ((polynomialUnderFunctor R).map ((polynomialUnderCoefficient R).app a)))

/-- The independent target sheet sign is evaluated at Laurent(b). -/
abbrev chart := BassMWholeNerve.coefficientModel P (β.app ((laurentUnderFunctor R).obj b))

/-- The Laurent reference is the actual postcomposition, without a base-source factorization. -/
abbrev laurentReference := polynomialReference P α f ≫ chart P β (b := b)

/-- One unreduced cylinder attachment and one tip, retaining the whole Laurent nerve. -/
abbrev scalar := firstSimplicial (polynomialReference P α f) (chart P β (b := b))
  (laurentReference P α β f) (Iso.refl _)

/-- The realization of the original single polynomial reference sheet with source chart `α` and
target chart `β`. -/
abbrev space := |scalar P α β f|

/-- The existing two-sheet evaluation restricts along the literal first summand. -/
def embed : C(space P α β f, CutOpenCarrier.space
    (polynomialReference P α f) (chart P β (b := b)) (laurentReference P α β f)
    (Iso.refl _) (Iso.refl _)) :=
  (SSet.toTop.map (left₁ (polynomialReference P α f) (chart P β (b := b))
    (laurentReference P α β f) (Iso.refl _) (Iso.refl _))).hom

/-- Include the entire original Laurent reference into the single polynomial sheet. -/
def laurent : C(|parameterSSet (laurentReference P α β f)|, space P α β f) :=
  (SSet.toTop.map (left₀ (polynomialReference P α f) (chart P β (b := b))
    (laurentReference P α β f) (Iso.refl _))).hom

/-- The original unreduced polynomial cylinder with its full reference input and unchanged
height. -/
def cylinder : C(|parameterSSet (polynomialReference P α f)| × I, space P α β f) where
  toFun z := DoubleCylinder.realizedCylinder
    (attaching (polynomialReference P α f) (chart P β (b := b))
      (laurentReference P α β f) (Iso.refl _)) (erase (polynomialReference P α f))
      (z.1, ULift.up z.2)
  continuous_toFun := by
    exact (DoubleCylinder.realizedCylinder
      (attaching (polynomialReference P α f) (chart P β (b := b))
        (laurentReference P α β f) (Iso.refl _))
      (erase (polynomialReference P α f))).hom.continuous.comp (by fun_prop)

/-- The original unreduced tip of the single polynomial reference sheet. -/
def tip : space P α β f :=
  SSet.toTop.map (right₀ (polynomialReference P α f) (chart P β (b := b))
    (laurentReference P α β f) (Iso.refl _)) (default : |tipSSet.{u + 1}|)

theorem contractibleSpace : ContractibleSpace (space P α β f) :=
  first_contractibleSpace (polynomialReference P α f) (chart P β (b := b))
    (laurentReference P α β f) (Iso.refl _)

/-- Evaluation remains defined on every scalar point and every genuine polynomial input. -/
def evaluate (n : ℕ) (z : space P α β f) :=
  nativeEval (polynomialReference P α f) (chart P β (b := b))
    (laurentReference P α β f) (Iso.refl _) (Iso.refl _) n (embed P α β f z)

theorem evaluate_laurent (n : ℕ) (y : |parameterSSet (laurentReference P α β f)|)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.space
        (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    evaluate P α β f n (laurent P α β f y) x =
      (Quillen.LoopPrespectrum.mappingConeInclusion (prespectrumMap (chart P β (b := b)))).map n
        (pointwisePrespectrumFamily (laurentReference P α β f) n y x) :=
  nativeEval_laurentInclusion _ _ _ _ _ n y x

theorem evaluate_cylinder (n : ℕ) (y : |parameterSSet (polynomialReference P α f)|)
    (t : I) (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.space
        (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    evaluate P α β f n (cylinder P α β f (y, t)) x =
      Quillen.ReducedMappingCone.cylinder _ _ ((prespectrumMap (chart P β (b := b))).map n)
        (t, pointwisePrespectrumFamily (polynomialReference P α f) n y x) :=
  nativeEval_cylinderMinus _ _ _ _ _ n y t x

/-- Compact parameter families use the existing exact cell-continuity theorem. -/
def compactFamily {S : Type u} [TopologicalSpace S] [CompactSpace S]
    (p : C(S, space P α β f)) (n : ℕ) :=
  compactNativeFamily (polynomialReference P α f) (chart P β (b := b))
    (laurentReference P α β f) (Iso.refl _) (Iso.refl _) ((embed P α β f).comp p) n

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialCone
