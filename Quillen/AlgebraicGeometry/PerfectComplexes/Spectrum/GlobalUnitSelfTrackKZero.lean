/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.GlobalUnit
public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarLaurentClassComparison
public import Quillen.Waldhausen.SConstruction.Iterated.SelfTrackKOperationObject

/-! # The original forward global-unit self-track on an object class

The actual flat-pullback spectrum homotopy evaluates on the original K-zero
object loop to the independent K-one class of the forward global unit on the
pulled-back perfect complex. This is an object evaluation, retaining the
original canonical zero rebasing and the original small-model comparison.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
  (q : (Γ(X, ⊤))ˣ) (K : Perfect Y)

/-- The actual right-unitor factors leave precisely the original forward unit component. -/
theorem perfectFlatPullbackUnitIso_app :
    (perfectFlatPullbackUnitIso f q).app K =
      (perfectGlobalUnitIso X q).app ((perfectFlatPullback f).obj K) := by
  apply Iso.ext
  simp [perfectFlatPullbackUnitIso]

/-- The original K-zero object loop evaluates to the forward scalar K-one class. -/
theorem perfectFlatUnitHomotopy_object :
    originalKSelfTrackOperation (perfectWaldhausen Y) (perfectWaldhausen X)
      (perfectFlatUnitHomotopy f q) 0 ((perfectWaldhausen Y).kZeroObjectClass K) =
      perfectGlobalUnitKOneClass X q ((perfectFlatPullback f).obj K) := by
  change originalKSelfTrackOperation (perfectWaldhausen Y) (perfectWaldhausen X)
    (exactOriginalPrespectrumIsoHomotopy _ _ (perfectFlatPullback_waldhausenExact f)
      (perfectFlatPullback_waldhausenExact f) (perfectFlatPullbackUnitIso f q)) 0 _ = _
  rw [originalKSelfTrackOperation_object, perfectFlatPullbackUnitIso_app]
  rfl

end Quillen.PerfectComplexes
