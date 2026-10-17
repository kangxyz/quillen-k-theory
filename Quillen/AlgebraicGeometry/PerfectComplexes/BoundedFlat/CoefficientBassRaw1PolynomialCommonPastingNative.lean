/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialCommonPasting

/-!
Compact native evaluation of the pasted three original polynomial cap cubes.
The scalar family, genuine polynomial input, and independent structure time
are retained exactly in every native degree.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialCommonPastingNative
open CoefficientBassRaw1PolynomialTripleRoutes CoefficientBassRaw1PolynomialCommonPasting
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

/-- Joint continuity of the actual pasted family with every genuine polynomial input. -/
def nativeFamily (n : ℕ) :
    C((Fin 3 → I) × (prespectrum V).space n,
      (CommonReferenceNerve.CutOpenCarrier.nativeCone J).space n) :=
  CoefficientBassRaw1PolynomialPostcomp.compactFamily P p₀ q₀ l β
    (family P α f negative) n

/-- The evaluator uses precisely the pasted scalar value in the original first sheet. -/
theorem nativeFamily_apply (n : ℕ) (z : Fin 3 → I) (x : (prespectrum V).space n) :
    nativeFamily P α f negative n (z, x) =
      CoefficientBassRaw1PolynomialPostcomp.evaluate P p₀ q₀ l β n
        (family P α f negative z) x := rfl

/-- The complete first scalar boundary word is preserved before native evaluation. -/
theorem nativeFamily_zero (n : ℕ) (r h : I) (x : (prespectrum V).space n) :
    nativeFamily P α f negative n (![0, r, h], x) =
      CoefficientBassRaw1PolynomialPostcomp.evaluate P p₀ q₀ l β n
        (leftWord P α f negative r h) x :=
  congrArg (fun y ↦ CoefficientBassRaw1PolynomialPostcomp.evaluate P p₀ q₀ l β n y x)
    (family_zero P α f negative r h)

/-- The complete opposite scalar boundary word keeps all of its original clocks. -/
theorem nativeFamily_one (n : ℕ) (r h : I) (x : (prespectrum V).space n) :
    nativeFamily P α f negative n (![1, r, h], x) =
      CoefficientBassRaw1PolynomialPostcomp.evaluate P p₀ q₀ l β n
        (rightWord P α f negative r h) x :=
  congrArg (fun y ↦ CoefficientBassRaw1PolynomialPostcomp.evaluate P p₀ q₀ l β n y x)
    (family_one P α f negative r h)

/-- All three coherence coordinates preserve the original native basepoint. -/
theorem nativeFamily_point (n : ℕ) (z : Fin 3 → I) :
    nativeFamily P α f negative n (z, (prespectrum V).point n) =
      (CommonReferenceNerve.CutOpenCarrier.nativeCone J).point n :=
  CoefficientBassRaw1PolynomialPostcomp.evaluate_point P p₀ q₀ l β
    n (family P α f negative z)

/-- Native structure time is independent of the three original coherence coordinates. -/
theorem nativeFamily_structure (n : ℕ) (z : Fin 3 → I)
    (x : (prespectrum V).space n) (t : I) :
    nativeFamily P α f negative (n + 1) (z, (prespectrum V).structureMap n x t) =
      (CommonReferenceNerve.CutOpenCarrier.nativeCone J).structureMap n
        (nativeFamily P α f negative n (z, x)) t :=
  CoefficientBassRaw1PolynomialPostcomp.evaluate_structure P p₀ q₀ l β
    n (family P α f negative z) x t

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialCommonPastingNative
