/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.GlobalUnitKOperation

/-! # Inverse-unit operation consumers retain arbitrary original K-zero and K-one classes -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes Quillen.Waldhausen.IteratedS
universe u
namespace QuillenTest.GlobalUnitKOperation

/-- The inverse-unit equation holds for any original K-zero class, not only an object class. -/
theorem inverse_unit_kzero {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (q : (Γ(X, ⊤))ˣ) (a : PerfectK Y 0) :
    originalKSelfTrackOperation (perfectWaldhausen Y) (perfectWaldhausen X)
        (perfectFlatUnitHomotopy f q⁻¹) 0 a =
      (originalKSelfTrackOperation (perfectWaldhausen Y) (perfectWaldhausen X)
        (perfectFlatUnitHomotopy f q) 0 a)⁻¹ :=
  perfectFlatUnitHomotopy_originalKOperation_inv f q 0 a

/-- The same theorem retains the original K-one input and K-two output. -/
theorem inverse_unit_kone {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (q : (Γ(X, ⊤))ˣ) (a : PerfectK Y 1) :
    originalKSelfTrackOperation (perfectWaldhausen Y) (perfectWaldhausen X)
        (perfectFlatUnitHomotopy f q⁻¹) 1 a =
      (originalKSelfTrackOperation (perfectWaldhausen Y) (perfectWaldhausen X)
        (perfectFlatUnitHomotopy f q) 1 a)⁻¹ :=
  perfectFlatUnitHomotopy_originalKOperation_inv f q 1 a

end QuillenTest.GlobalUnitKOperation
