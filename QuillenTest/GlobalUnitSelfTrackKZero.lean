/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.GlobalUnitSelfTrackKZero

/-! # Forward global-unit evaluation on the actual original object class -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes
open Quillen.Waldhausen.IteratedS
universe u
namespace QuillenTest.GlobalUnitSelfTrackKZero

/-- This is the original forward q class, on the actual flat pullback of the supplied complex. -/
theorem original_forward_unit_object {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (q : (Γ(X, ⊤))ˣ) (K : Perfect Y) :
    originalKSelfTrackOperation (perfectWaldhausen Y) (perfectWaldhausen X)
      (perfectFlatUnitHomotopy f q) 0 ((perfectWaldhausen Y).kZeroObjectClass K) =
      perfectGlobalUnitKOneClass X q ((perfectFlatPullback f).obj K) :=
  perfectFlatUnitHomotopy_object f q K

end QuillenTest.GlobalUnitSelfTrackKZero
