/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassLaurentCompositionCarrier
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTargetChartNative

/-! The original chart square followed by Laurent composition on genuine polynomial input. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1ChartCompositionProduct
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b c d : Under R} (f : a ⟶ b) (p : b ⟶ c) (q : c ⟶ d)

/-- The full source reference of the original chart naturality square. -/
abbrev chartReference := NativeSquareFiveSimplex.source
  (coefficientMap P ((laurentUnderFunctor R).map f)) (coefficientMap P (β.app a))

/-- All five original square nodes retain their prescribed reference isomorphisms. -/
abbrev chartNodes := NativeSquareFiveSimplex.nodes
  (coefficientMap P ((laurentUnderFunctor R).map f)) (coefficientMap P (β.app a))
  (coefficientMap P (β.app b)) (coefficientMap P ((polynomialUnderFunctor R).map f))
  (coefficientMap_naturality P β f)

/-- The original two binary square paths, without changing their midpoint clock. -/
def chartFamily : C(I, |parameterSSet (chartReference P β f)|) :=
  (parameter (chartReference P β f) (chartNodes P β f)).comp
    NativeSquareFiveSimplex.parameter.toContinuousMap

/-- The product reference still has arbitrary polynomial input. -/
abbrev reference := chartReference P β f ≫
  CoefficientBassLaurentCompositionCarrier.reference P p q

/-- The fifteen-node product keeps square time and composition time independent. -/
def family : C(I × I, |parameterSSet (reference P β f p q)|) :=
  (FiniteParameter.parameter (chartReference P β f) (reference P β f p q)
    (fun N j ↦ CommonReferenceProduct.node (reference P β f p q)
      (chartReference P β f) (CoefficientBassLaurentCompositionCarrier.reference P p q)
      (Iso.refl _) N (CoefficientBassLaurentCompositionCarrier.nodes P p q j))).comp
    { toFun := fun z ↦ (chartFamily P β f z.2, binaryPath (k := 2) 0 1 2 z.1)
      continuous_toFun := ((chartFamily P β f).continuous.comp continuous_snd).prodMk
        ((binaryPath (k := 2) 0 1 2).continuous.comp continuous_fst) }

/-- The first factor is exactly the original chart square at every native level. -/
theorem chartFamily_native (n : ℕ) (t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    pointwisePrespectrumFamily (chartReference P β f) n (chartFamily P β f t) x =
      (boundedFlatPerfectPrespectrumSquareHomotopy
        (coefficientMap P ((laurentUnderFunctor R).map f)) (coefficientMap P (β.app a))
        (coefficientMap P (β.app b))
        (coefficientMap P ((polynomialUnderFunctor R).map f))
        (coefficientMap_naturality P β f)).level n (t, x) := by
  dsimp only [chartFamily, ContinuousMap.comp_apply]
  rw [pointwisePrespectrumFamily_parameter, prespectrumFamily_eq]
  exact NativeSquareFiveSimplex.native _ _ _ _ _ n t x

/-- The actual chart-square input feeds the original Laurent composition, with both clocks. -/
theorem family_native (n : ℕ) (r t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    pointwisePrespectrumFamily (reference P β f p q) n (family P β f p q (r, t)) x =
      (boundedFlatCoefficientLaurentCompositionHomotopy P p q).level n
        (r, (boundedFlatPerfectPrespectrumSquareHomotopy
          (coefficientMap P ((laurentUnderFunctor R).map f)) (coefficientMap P (β.app a))
          (coefficientMap P (β.app b))
          (coefficientMap P ((polynomialUnderFunctor R).map f))
          (coefficientMap_naturality P β f)).level n (t, x)) := by
  dsimp only [family, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  rw [CoefficientBassSeedTargetChartNative.finite_product_native]
  have h := CoefficientBassLaurentCompositionCarrier.family_native P p q n r
    (pointwisePrespectrumFamily (chartReference P β f) n (chartFamily P β f t) x)
  rw [← pointwisePrespectrumFamily_eq_compact] at h
  dsimp only [CoefficientBassLaurentCompositionCarrier.family,
    ContinuousMap.comp_apply] at h
  rw [pointwisePrespectrumFamily_parameter] at h
  exact h.trans (congrArg
    (fun y ↦ (boundedFlatCoefficientLaurentCompositionHomotopy P p q).level n (r, y))
    (chartFamily_native P β f n t x))

end Quillen.PerfectComplexes.CoefficientBassRaw1ChartCompositionProduct
