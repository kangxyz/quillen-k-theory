/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassLaurentProjectionScalar
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCutOpenPrecompNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveWhiskered

/-! Whole Laurent comparison restriction to genuine polynomial chart inputs. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1LaurentChartRestriction
open CommonReferenceNerve
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (α β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b : Under R} (u : a ⟶ b)

/-- The source chart acts on arbitrary polynomial inputs. -/
abbrev chart := BassMWholeNerve.coefficientModel P (β.app a)

/-- All eighteen nodes retain their entire precomposed reference isomorphisms. -/
def nodes := fun i : Fin 18 ↦ precompNode (chart P β (a := a))
  (CoefficientBassLaurentProjectionScalar.nodes P α u i)

/-- The original comparison surface is mapped without changing either clock. -/
def family := (mapParameter (precompNode (chart P β (a := a)))).comp
  (CoefficientBassLaurentProjectionScalar.family P α u)

/-- The full finite simplex, including its interior, is preserved. -/
theorem family_parameter (z : I × I) : family P α β u z =
    parameter (chart P β (a := a) ≫ CoefficientBassLaurentProjectionScalar.reference P α u)
      (nodes P α β u) (CoefficientBassLaurentProjectionScalar.scalarComparison z) := by
  exact mapParameter_parameter (precompNode (chart P β (a := a)))
    (CoefficientBassLaurentProjectionScalar.nodes P α u)
    (CoefficientBassLaurentProjectionScalar.scalarComparison z)

/-- Every polynomial native input is evaluated through the actual source chart map. -/
theorem family_native (n : ℕ) (z : I × I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    pointwisePrespectrumFamily
      (chart P β (a := a) ≫ CoefficientBassLaurentProjectionScalar.reference P α u)
      n (family P α β u z) x =
    pointwisePrespectrumFamily (CoefficientBassLaurentProjectionScalar.reference P α u)
      n (CoefficientBassLaurentProjectionScalar.family P α u z)
      ((boundedFlatPerfectPrespectrumMap (coefficientMap P (β.app a))).map n x) :=
  CutOpenPrecomp.pointwise_precomp (chart P β (a := a))
    (CoefficientBassLaurentProjectionScalar.reference P α u) n
    (CoefficientBassLaurentProjectionScalar.family P α u z) x

end Quillen.PerfectComplexes.CoefficientBassRaw1LaurentChartRestriction
