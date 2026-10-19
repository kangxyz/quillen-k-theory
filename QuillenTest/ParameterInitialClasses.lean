/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterInitialPerfectClasses

/-! # Literal initial inclusions and original degree-zero classes -/
noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.LoopPrespectrum Quillen.KTheory.Bass Quillen.Waldhausen.IteratedS
open Quillen.KTheory.Bass.SchemeNaturalSeed Quillen.PerfectComplexes
open GlobalSectionChangeIndex ParameterLaurentTrack
universe u
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

example (T : Q.left.Opens) (d : ℤ) :
    (stableHomotopyFunctor d).map
        ((currentInitial (ParameterAuxiliarySupport.fiberAction f.left T)).app
          (specUnder.obj (Under.mk (𝟙 _)))) ≫
        (ParameterAuxiliaryCurrentFiber.currentFineSupportComparison f T
          (Under.mk (𝟙 _)) d).hom =
      (stableHomotopyFunctor d).map
          (prespectrumMap ((GlobalAuxiliaryParameterCoefficient.fiberComparison f T).app
            (Under.mk (𝟙 _)))) ≫
        (stableHomotopyFunctor d).map
          ((boundedFlatCoefficientSupportedFiberBassTelescopeInclusion f T 0).app
            (Under.mk (𝟙 _))) :=
  ParameterAuxiliaryCurrentFiber.current_fine_initial_fiber f T (Under.mk (𝟙 _)) d

example (T : Q.left.Opens) (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ)
    (x : ((ParameterAuxiliarySupport.openModel f.left T).obj (specUnder.obj a)).waldhausen.K n) :
    (ParameterAuxiliaryCurrentFiber.currentFineOpenComparison f T a (n : ℤ)).hom
        (currentModelClass (ParameterAuxiliarySupport.openModel f.left T)
          (ParameterAuxiliarySupport.openAction f.left T) (specUnder.obj a) n x) =
      (stableHomotopyFunctor (n : ℤ)).map
        ((boundedFlatCoefficientSupportedFullOpenBassTelescopeInclusion f T 0).app a)
        (modelKStableEquiv (boundedFlatCoefficientSupportedFullOpenModel f T a) n
          (Additive.ofMul (Quillen.Waldhausen.KMap
            ((GlobalAuxiliaryParameterCoefficient.openComparison f T).app a).exact n x))) :=
  ParameterAuxiliaryCurrentFiber.current_fine_open_modelClass f T a n x

example [CompactSpace Q.left] (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (x : ((ParameterModels.supported f.left).obj (specUnder.obj a)).waldhausen.K 0) :
    (ParameterFullCurrentNull.currentFineSupportComparison f a 0).hom
        (currentModelClass (ParameterModels.supported f.left) (supportedTrack f.left)
          (specUnder.obj a) 0 x) =
      (stableHomotopyFunctor 0).map
        ((boundedFlatCoefficientSupportedBassTelescopeInclusion f 0).app a)
        ((boundedFlatCoefficientSupportedBassBottomZeroIso f a).hom
          (Additive.ofMul (boundedFlatCoefficientSupportedPerfectKEquiv f a 0
            (Quillen.Waldhausen.KMap
              (((parameterSupportedRowIso f).hom ≫ supportedRowRestriction f).app a).exact
              0 x)))) :=
  ParameterFullCurrentNull.current_fine_originalSupportedZeroClass f a x
