/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialOrdinaryMap
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPostcompNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCutOpenPrecompNative

/-! Native evaluation of the complete source-projected polynomial and Laurent references. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialOrdinaryMap
open BassH0Merge CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
open BassProjectionPath.WholeReference CoefficientBassRaw1PolynomialSourceProjection
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)
local notation "E" => input P p q w
local notation "F" => CoefficientBassRaw1PolynomialSourceProjection.polynomial P p q w
local notation "A" => sourceProjection P (a := a)
local notation "Jd" => targetProjection P (d := d)

/-- The target polynomial vertex evaluates on the genuine source-projected native input. -/
theorem polynomial_native (n : ℕ) (y : |parameterSSet F|)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    pointwisePrespectrumFamily (E ≫ Jd) n (polynomial P p q w y) x =
      pointwisePrespectrumFamily F n y ((prespectrumMap A).map n x) := by
  obtain ⟨k, ns, z, rfl⟩ := exists_parameter F y
  change pointwisePrespectrumFamily (E ≫ Jd) n (mapParameter _ (parameter F ns z)) x = _
  rw [mapParameter_parameter, pointwisePrespectrumFamily_parameter,
    pointwisePrespectrumFamily_parameter]
  exact (congrArg (fun h ↦ h (z, x))
    (prespectrumFamily_reanchor (polynomialIso P p q w)
      (fun i ↦ precompNode A (ns i)) n)).trans (prespectrumFamily_precomp ns A n z x)

variable (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (hd : coefficientMap P (β.app d) ≫ polynomialProjection P d = laurentProjection P d)
local notation "J" => BassMWholeNerve.coefficientModel P (β.app d)
local notation "G" => F ≫ J

/-- Laurent transport preserves its complete native family after the actual source projection. -/
theorem laurent_native (n : ℕ) (y : |parameterSSet G|)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    pointwisePrespectrumFamily (BassProjectionPath.WholeReference.reference P d E) n
        (laurent P p q w β hd y) x =
      pointwisePrespectrumFamily G n y ((prespectrumMap A).map n x) := by
  obtain ⟨k, ns, z, rfl⟩ := exists_parameter G y
  change pointwisePrespectrumFamily _ n (mapParameter _ (parameter G ns z)) x = _
  rw [mapParameter_parameter, pointwisePrespectrumFamily_parameter,
    pointwisePrespectrumFamily_parameter]
  exact (congrArg (fun h ↦ h (z, x))
    (prespectrumFamily_reanchor (laurentIso P p q w β hd)
      (fun i ↦ precompNode A (ns i)) n)).trans (prespectrumFamily_precomp ns A n z x)

/-- The original first sheet retains its complete Laurent inclusion value. -/
theorem evaluate_laurent (n : ℕ) (y : |parameterSSet G|)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a))))).space n) :
    CoefficientBassRaw1PolynomialPostcomp.evaluate P p q w β n
      (SSet.toTop.map (left₀ F J G (Iso.refl _)) y) x =
      (mappingConeInclusion (prespectrumMap J)).map n (pointwisePrespectrumFamily G n y x) :=
  nativeEval_laurentInclusion F J G (Iso.refl _) (Iso.refl _) n y x

/-- The genuine polynomial input and original cylinder height are both unchanged. -/
theorem evaluate_cylinder (n : ℕ) (y : |parameterSSet F|) (t : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a))))).space n) :
    CoefficientBassRaw1PolynomialPostcomp.evaluate P p q w β n
      (DoubleCylinder.realizedCylinder (attaching F J G (Iso.refl _)) (erase F)
        (y, ULift.up t)) x =
      ReducedMappingCone.cylinder _ _ ((prespectrumMap J).map n)
        (t, pointwisePrespectrumFamily F n y x) :=
  nativeEval_cylinderMinus F J G (Iso.refl _) (Iso.refl _) n y t x

/-- The same first-sheet tip evaluates to the original native cone point. -/
theorem evaluate_tip (n : ℕ)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a))))).space n) :
    CoefficientBassRaw1PolynomialPostcomp.evaluate P p q w β n
      (SSet.toTop.map (right₀ F J G (Iso.refl _)) (default : |tipSSet.{u+1}|)) x =
      (mappingCone (prespectrumMap J)).point n :=
  nativeEval_tipMinus F J G (Iso.refl _) (Iso.refl _) n x

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialOrdinaryMap
