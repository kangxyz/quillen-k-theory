/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialCommonPastingSides
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialCommonPastingLaurentFace
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialCommonPastingTop
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialCommonPastingNative

/-!
# All six faces of the actual polynomial paste

The same chosen three-square paste is tested on both polynomial charts, at every scalar
point and every genuine polynomial native input. The complete bottom is the old Laurent
family, not just its endpoints. Native structure time remains independent of all three
coherence coordinates.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace QuillenTest.Raw1PolynomialPasting
open Quillen.PerfectComplexes
open CoefficientBassRaw1PolynomialTripleRoutes CoefficientBassRaw1PolynomialCommonPasting
open CoefficientBassRaw1PolynomialCommonPastingNative CommonReferenceNerve
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b : Under R} (f : a ⟶ b) (negative : Bool)
local notation "β" => chartChoice negative
local notation "p₀" => CategoryTheory.NatTrans.app (polynomialUnderCoefficient R) a
local notation "q₀" => CategoryTheory.NatTrans.app α a
local notation "l" => CategoryTheory.Functor.map (laurentUnderFunctor R) f
local notation "V" => modelOf (boundedFlatPerfectWaldhausen
  (space (op P, CategoryTheory.Functor.obj (polynomialUnderFunctor R) a)))
local notation "J" => BassMWholeNerve.coefficientModel P
  (CategoryTheory.NatTrans.app β (CategoryTheory.Functor.obj (laurentUnderFunctor R) b))
local notation "ev" => CoefficientBassRaw1PolynomialPostcomp.evaluate P p₀ q₀ l β

/-- The first original word retains its complete nested clocks at every native input. -/
theorem nativeZeroFace (n : ℕ) (r h : I) (x : (prespectrum V).space n) :
    nativeFamily P α f negative n (![0, r, h], x) =
      ev n (leftWord P α f negative r h) x :=
  nativeFamily_zero P α f negative n r h x

example (n : ℕ) (r h : I) (x : (prespectrum V).space n) :
    nativeFamily P α f negative n (![1, r, h], x) =
      ev n (rightWord P α f negative r h) x :=
  nativeFamily_one P α f negative n r h x

-- Both side faces are fixed as whole height paths, for arbitrary pasting coordinate.
example (n : ℕ) (r h : I) (x : (prespectrum V).space n) :
    nativeFamily P α f negative n (![r, 0, h], x) =
      ev n (leftWord P α f negative 0 h) x :=
  congrArg (fun y ↦ ev n y x) (family_source P α f negative r h)

example (n : ℕ) (r h : I) (x : (prespectrum V).space n) :
    nativeFamily P α f negative n (![r, 1, h], x) =
      ev n (leftWord P α f negative 1 h) x :=
  congrArg (fun y ↦ ev n y x) (family_target P α f negative r h)

-- Every point of the full bottom retains the original Laurent18 restriction.
example (n : ℕ) (r s : I) (x : (prespectrum V).space n) :
    nativeFamily P α f negative n (![r, s, 0], x) =
      ev n (CoefficientBassRaw1PolynomialCapLowerFaces.laurent P α β f
        (mapParameter (CommonReferenceProduct.reanchor
          (CoefficientBassRaw1PolynomialReference.referenceIso P α β f).symm)
          (CoefficientBassRaw1LaurentChartRestriction.family P α β f (r, s)))) x :=
  congrArg (fun y ↦ ev n y x) (family_bottom_restricted P α f negative r s)

-- The top uses the actual unreduced common-sheet tip before native evaluation.
example (n : ℕ) (r s : I) (x : (prespectrum V).space n) :
    nativeFamily P α f negative n (![r, s, 1], x) =
      ev n (CoefficientBassRaw1PolynomialPostcomp.tip P p₀ q₀ l β) x :=
  congrArg (fun y ↦ ev n y x)
    (CoefficientBassRaw1PolynomialCommonPastingTop.family_top P α f negative r s)

-- Two independently proved faces agree on their complete bottom/zero intersection.
example (r : I) : leftWord P α f negative r 0 =
    CoefficientBassRaw1PolynomialCapLowerFaces.laurent P α β f
      (mapParameter (CommonReferenceProduct.reanchor
        (CoefficientBassRaw1PolynomialReference.referenceIso P α β f).symm)
        (CoefficientBassRaw1LaurentChartRestriction.family P α β f (0, r))) :=
  (family_zero P α f negative r 0).symm.trans
    (family_bottom_restricted P α f negative 0 r)

-- All coherence coordinates preserve the original native point in every degree.
example (n : ℕ) (z : Fin 3 → I) :
    nativeFamily P α f negative n (z, (prespectrum V).point n) =
      (CommonReferenceNerve.CutOpenCarrier.nativeCone J).point n :=
  nativeFamily_point P α f negative n z

-- Native structure time t is independent of all three coherence coordinates z.
example (n : ℕ) (z : Fin 3 → I) (x : (prespectrum V).space n) (t : I) :
    nativeFamily P α f negative (n + 1) (z, (prespectrum V).structureMap n x t) =
      (CommonReferenceNerve.CutOpenCarrier.nativeCone J).structureMap n
        (nativeFamily P α f negative n (z, x)) t :=
  nativeFamily_structure P α f negative n z x t

end QuillenTest.Raw1PolynomialPasting

open Quillen.PerfectComplexes

#print axioms CoefficientBassRaw1PolynomialTripleFiller.extension
#print axioms CoefficientBassRaw1PolynomialCommonPasting.pasted
#print axioms CoefficientBassRaw1PolynomialCommonPasting.family
#print axioms CoefficientBassRaw1PolynomialCommonPasting.family_zero
#print axioms CoefficientBassRaw1PolynomialCommonPasting.family_one
#print axioms CoefficientBassRaw1PolynomialCommonPasting.family_source
#print axioms CoefficientBassRaw1PolynomialCommonPasting.family_target
#print axioms CoefficientBassRaw1PolynomialCommonPastingBottom.family_bottom
#print axioms CoefficientBassRaw1PolynomialCommonPasting.family_bottom_restricted
#print axioms CoefficientBassRaw1PolynomialCommonPastingTop.family_top
#print axioms CoefficientBassRaw1PolynomialCommonPastingNative.nativeFamily
#print axioms CoefficientBassRaw1PolynomialCommonPastingNative.nativeFamily_point
#print axioms CoefficientBassRaw1PolynomialCommonPastingNative.nativeFamily_structure
