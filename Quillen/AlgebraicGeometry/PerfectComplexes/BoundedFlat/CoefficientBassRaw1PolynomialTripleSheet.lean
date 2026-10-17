/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPostcompNative
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCutOpenCompactFamily

/-! The actual polynomial triple sheet supports compact based native families. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u v
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialPostcomp
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)
  (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
local notation "F" => reference P p q w
local notation "J" => BassMWholeNerve.coefficientModel P (β.app d)
local notation "G" => F ≫ J
local notation "V" => modelOf (boundedFlatPerfectWaldhausen
  (space (op P, CategoryTheory.Functor.obj (polynomialUnderFunctor R) a)))

/-- Contractibility belongs to this literal first sheet with its original chart attachment. -/
theorem carrier_contractible : ContractibleSpace (carrier P p q w β) :=
  first_contractibleSpace F J G (Iso.refl _)

/-- Literal first-sheet inclusion into the existing evaluator, with no changed scalar points. -/
def embed : C(carrier P p q w β, CutOpenCarrier.space F J G (Iso.refl _) (Iso.refl _)) :=
  (SSet.toTop.map (left₁ F J G (Iso.refl _) (Iso.refl _))).hom

/-- Every fixed scalar point preserves the original native basepoint. -/
theorem evaluate_point (n : ℕ) (z : carrier P p q w β) :
    evaluate P p q w β n z ((prespectrum V).point n) = (nativeCone J).point n :=
  nativeEval_point F J G (Iso.refl _) (Iso.refl _) n (embed P p q w β z)

/-- The independent structure time is preserved for every full native input. -/
theorem evaluate_structure (n : ℕ) (z : carrier P p q w β)
    (x : (prespectrum V).space n) (t : I) :
    evaluate P p q w β (n + 1) z ((prespectrum V).structureMap n x t) =
      (nativeCone J).structureMap n (evaluate P p q w β n z x) t :=
  nativeEval_structure F J G (Iso.refl _) (Iso.refl _) n (embed P p q w β z) x t

/-- Every actual compact scalar family has joint native continuity in all degrees. -/
def compactFamily {S : Type v} [TopologicalSpace S] [CompactSpace S]
    (f : C(S, carrier P p q w β)) (n : ℕ) :
    C(S × (prespectrum V).space n, (nativeCone J).space n) :=
  compactNativeFamily F J G (Iso.refl _) (Iso.refl _) ((embed P p q w β).comp f) n

/-- Packaging retains the exact scalar value and the separate arbitrary native input. -/
theorem compactFamily_apply {S : Type v} [TopologicalSpace S] [CompactSpace S]
    (f : C(S, carrier P p q w β)) (n : ℕ) (s : S) (x : (prespectrum V).space n) :
    compactFamily P p q w β f n (s, x) = evaluate P p q w β n (f s) x := rfl

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialPostcomp
