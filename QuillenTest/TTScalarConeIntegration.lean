/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import QuillenTest.TTStableSeedIntegration
public import QuillenTest.AdditivityPushoutTransformation
public import QuillenTest.CoefficientBassPositiveSupport
public import QuillenTest.ExactSelfTrackStableOperation
public import QuillenTest.FactorizationConeFunctor
public import QuillenTest.GlobalUnitKOperation
public import QuillenTest.GlobalUnitSelfTrackKZero
public import QuillenTest.GlobalUnitStableOperation
public import QuillenTest.MWholeNerveWhiskeredStart
public import QuillenTest.MWholeNerveWhiskeredTerminal
public import QuillenTest.NativeTautologicalCoefficientConeFunctor
public import QuillenTest.ScalarCofiberFunctor
public import QuillenTest.ScalarConeFunctor
public import QuillenTest.SelfTrackKOperationObject
public import QuillenTest.SelfTrackKOperationPath
public import QuillenTest.SelfTrackRelativeHomotopy
public import QuillenTest.SelfTrackStableConcatenation
public import QuillenTest.SelfTrackStableTimeOperations
public import QuillenTest.SelfTrackTimeOperations

/-! # Joint original scalar, cone and inverse-unit operation consumers -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes Quillen.Waldhausen.IteratedS
universe u
namespace QuillenTest.TTScalarConeIntegration

/-- Joint imports retain the inverse-unit formula on an arbitrary original K-zero class. -/
theorem original_kzero_inverse_unit {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (q : (Γ(X, ⊤))ˣ) (a : PerfectK Y 0) :
    originalKSelfTrackOperation (perfectWaldhausen Y) (perfectWaldhausen X)
        (perfectFlatUnitHomotopy f q⁻¹) 0 a =
      (originalKSelfTrackOperation (perfectWaldhausen Y) (perfectWaldhausen X)
        (perfectFlatUnitHomotopy f q) 0 a)⁻¹ :=
  perfectFlatUnitHomotopy_originalKOperation_inv f q 0 a

end QuillenTest.TTScalarConeIntegration
