/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarCofiberFunctor
public import QuillenTest.ScalarConeFunctor
public import QuillenTest.FactorizationConeFunctor
/-! The original cylinder maps and literal cone quotient form a genuine cofibration sequence. -/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Quillen.PerfectComplexes
open Quillen.Waldhausen
universe u
namespace QuillenTest.ScalarCofiberFunctor
variable (X : Scheme.{u}) (r : Γ(X, ⊤))

/-- The natural inclusion component remains the old actual extension inclusion. -/
theorem original_inclusion (K : Perfect X) :
    (perfectScalarInclusionNat X r).app K = perfectScalarInclusion X r K := rfl

/-- The entire factorization gives the actual original scalar natural transformation. -/
theorem original_scalar_factorization :
    perfectScalarInclusionNat X r ≫ perfectScalarProjectionNat X r =
      perfectGlobalScalar X r :=
  perfectScalarInclusionNat_projection X r

/-- The cone sequence uses the original fine structure and inherited relative cofibrations. -/
theorem original_fine_cofibration_sequence :
    Additivity.IsCofibrationSequence (perfectWaldhausen X) (perfectWaldhausen X)
      (perfectScalarInclusionNat X r) (perfectScalarConeProjectionNat X r) :=
  perfectScalarCofibrationSequence X r

end QuillenTest.ScalarCofiberFunctor
