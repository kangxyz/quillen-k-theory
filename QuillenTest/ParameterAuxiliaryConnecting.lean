/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliaryFineConnectingComparison

/-! # Auxiliary signed connecting maps through the actual same-null zigzag -/
noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.LoopPrespectrum Quillen.PerfectComplexes
open ParameterAuxiliaryCurrentFiber
universe u
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left] (T : Q.left.Opens) [CompactSpace T]

example (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    currentConnecting f T a d ≫ (currentFineSupportComparison f T a d).hom =
      (currentFineOpenComparison f T a (d + 1)).hom ≫
        boundedFlatCoefficientAuxiliaryLocalizationConnecting f T a d :=
  current_fine_connecting f T a d

example (d : ℤ) :
    currentConnecting f T (Under.mk (𝟙 _)) d ≫
        (currentFineSupportComparison f T (Under.mk (𝟙 _)) d).hom =
      (currentFineOpenComparison f T (Under.mk (𝟙 _)) (d + 1)).hom ≫
        boundedFlatCoefficientAuxiliaryLocalizationConnecting f T (Under.mk (𝟙 _)) d :=
  current_fine_connecting f T (Under.mk (𝟙 _)) d

example (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    boundedFlatCoefficientAuxiliaryLocalizationConnecting f T a d ≫
        (stableHomotopyFunctor d).map
          (boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenFiberMap f T a) =
      stableFiberConnecting
        ((boundedFlatCoefficientSupportedAmbientBassTelescopeFullOpen f T).app a) d :=
  boundedFlatCoefficientAuxiliaryLocalizationConnecting_comp_fiberMap f T a d
