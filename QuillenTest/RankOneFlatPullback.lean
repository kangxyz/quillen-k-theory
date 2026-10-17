/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.RankOneFlatPullback
public import Quillen.AlgebraicGeometry.PerfectComplexes.FlatPullback
public import Quillen.Waldhausen.GrothendieckComparison.ObjectNaturality

/-! The actual flat K-map retains the original rank-one object class. -/
@[expose] public section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes Quillen.Waldhausen
universe u
namespace QuillenTest.RankOneFlatPullback

/-- Original flat pullback, including its canonical zero rebase, preserves the structure class. -/
theorem original_rankOne_class {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    perfectKFlatPullback f 0 ((perfectWaldhausen Y).kZeroObjectClass (rankOnePerfect Y)) =
      (perfectWaldhausen X).kZeroObjectClass (rankOnePerfect X) :=
  (KMap_kZeroObjectClass (perfectFlatPullback_waldhausenExact f) _).trans
    ((perfectWaldhausen X).kZeroObjectClass_iso (rankOnePerfectFlatPullbackIso f))

end QuillenTest.RankOneFlatPullback
