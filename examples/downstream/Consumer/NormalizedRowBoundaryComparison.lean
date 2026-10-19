/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliaryNormalizedRowBoundaryComparison

/-! The actual row's intrinsic boundary agrees with the original cone boundary on all classes. -/
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.PerfectComplexes
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.PerfectComplexes.GlobalSectionChangeIndex.ParameterAuxiliarySupport
open Quillen.PerfectComplexes.ParameterAuxiliaryNormalizedRowLocalization
universe u

example {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
    [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
    [QuasiSeparatedSpace Q.left] (T : Q.left.Opens) [CompactSpace T]
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ)
    (x : stableHomotopyGroup
      (ParameterTensorNormalizedRowPresentation.supported (inverseOpen f.left T).ι
        (specUnder.obj a)) (d + 1)) :
    (normalizedFineSupportComparison f T a d).hom
        (normalizedPresentationConnecting f T a d x) =
      boundedFlatCoefficientAuxiliaryLocalizationConnecting f T a d
        ((normalizedFineOpenComparison f T a (d + 1)).hom x) :=
  ConcreteCategory.congr_hom (normalizedPresentationConnecting_fine f T a d) x
