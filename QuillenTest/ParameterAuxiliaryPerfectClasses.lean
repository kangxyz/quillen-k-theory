/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliaryPerfectClasses
import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientAuxiliaryPerfectMaps
import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientAuxiliaryPerfectRestriction

/-! # Original auxiliary perfect classes and both geometric arrows -/
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes
open Quillen.LoopPrespectrum Quillen.KTheory.Bass.SchemeNaturalSeed
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open GlobalSectionChangeIndex ParameterAuxiliarySupport GlobalAuxiliaryParameterCoefficient
open ParameterAuxiliaryCurrentFiber
universe u
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left] (T : Q.left.Opens)

example (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ)
    (x : ((fiber f.left T).obj (specUnder.obj a)).waldhausen.K n) :
    (currentFineSupportComparison f T a (n : ℤ)).hom
        (currentModelClass (fiber f.left T) (fiberAction f.left T) (specUnder.obj a) n x) =
      (stableHomotopyFunctor (n : ℤ)).map
        ((boundedFlatCoefficientSupportedFiberBassTelescopeInclusion f T 0).app a)
        (auxiliaryFiberPerfectStableEquiv f T a n
          (Additive.ofMul (auxiliaryFiberPerfectKEquiv f T a n
            (Quillen.Waldhausen.KMap ((fiberComparison f T).app a).exact n x)))) :=
  current_fine_fiber_perfectClass f T a n x

example (x : ((openModel f.left T).obj (specUnder.obj
    (Under.mk (𝟙 (CommRingCat.of (ULift.{u} ℤ)))))).waldhausen.K 0) :
    (currentFineOpenComparison f T (Under.mk (𝟙 _)) 0).hom
        (currentModelClass (openModel f.left T) (openAction f.left T)
          (specUnder.obj (Under.mk (𝟙 _))) 0 x) =
      (stableHomotopyFunctor 0).map
        ((boundedFlatCoefficientSupportedFullOpenBassTelescopeInclusion f T 0).app
          (Under.mk (𝟙 _)))
        (auxiliaryOpenPerfectStableEquiv f T (Under.mk (𝟙 _)) 0
          (Additive.ofMul (auxiliaryOpenPerfectKEquiv f T (Under.mk (𝟙 _)) 0
            (Quillen.Waldhausen.KMap ((openComparison f T).app (Under.mk (𝟙 _))).exact 0 x)))) :=
  current_fine_open_perfectClass f T _ 0 x

example (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ)
    (x : (boundedFlatCoefficientSupportedFiberModel f T a).waldhausen.K n) :
    auxiliaryAmbientPerfectKEquiv T a n
        (Quillen.Waldhausen.KMap
          (boundedFlatCoefficientSupportedFiberForgetModelMap f T a).exact n x) =
      perfectSupportedUnionKMap
        (AlgebraicGeometry.Scheme.BaseChange.Coefficients.schemeMap f a)
        (boundedFlatCoefficientSupportOpen Q T a) n (auxiliaryFiberPerfectKEquiv f T a n x) :=
  auxiliaryPerfectKEquiv_enlargement f T a n x

example (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ)
    (x : (boundedFlatCoefficientSupportedAmbientModel T a).waldhausen.K n) :
    auxiliaryOpenPerfectKEquiv f T a n
        (Quillen.Waldhausen.KMap
          (boundedFlatCoefficientSupportedOpenRestriction_fine_exact f T a) n x) =
      perfectSupportedKRestrict
        (AlgebraicGeometry.Scheme.BaseChange.Coefficients.schemeMap f a)
        (boundedFlatCoefficientSupportOpen Q T a) n (auxiliaryAmbientPerfectKEquiv T a n x) :=
  auxiliaryPerfectKEquiv_restriction f T a n x
