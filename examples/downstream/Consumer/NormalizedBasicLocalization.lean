/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterNormalizedBasicLocalization

/-! # The actual basic localization with independent ambient middle and open objects -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open AlgebraicGeometry.Scheme.Products
open Quillen.PerfectComplexes
namespace Consumer.NormalizedBasicLocalization
universe u

/-- The displayed basic lift, with its own maps and original null, is invertible in every degree. -/
theorem basic_lift_signed_iso (Q : Scheme.{u}) (U : Q.Opens)
    [CompactSpace Q] [QuasiSeparatedSpace Q] [CompactSpace U] (d : ℤ) :
    IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift
        (ParameterNormalizedBasicLocalization.restriction U.ι (op integerBase))
        (ParameterTensorNormalizedRowPresentation.forget U.ι (op integerBase))
        (ParameterNormalizedBasicLocalization.basicNull Q U (op integerBase)))) :=
  ParameterNormalizedBasicLocalization.basicLift_integer_isStableEquivalence Q U d

end Consumer.NormalizedBasicLocalization
