/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NormalizedPullbackCoherence
public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.BoundedFlatPullback

/-! Consumers retain the original raw spectrum map and the entire geometric comparison line. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen.IteratedS Quillen.PerfectComplexes
universe u
namespace QuillenTest.NormalizedPullbackCoherence

open Quillen

/-- The normalized functor induces precisely the existing original raw bounded-flat map. -/
theorem original_raw_map {X Y : Scheme.{u}} (f : X ⟶ Y) :
    originalPrespectrumMap (boundedFlatPerfectWaldhausen Y) (boundedFlatPerfectWaldhausen X)
      (boundedFlatNormalizedPullback_exact f) (boundedFlatNormalizedPullback_obj_zero f) =
        boundedFlatPerfectPrespectrumMap f := rfl

/-- Every independent comparison time and path time fixes the actual original zero line. -/
theorem original_based_comparison {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) (n : ℕ) (r s : unitInterval) :
    (boundedFlatNormalizedTriplePasting f g h).level n
      (r, (s, (originalPrespectrum (boundedFlatPerfectWaldhausen T)).point n)) =
        (originalPrespectrum (boundedFlatPerfectWaldhausen X)).point n :=
  ((boundedFlatNormalizedTriplePasting f g h).at r).at_point n s

end QuillenTest.NormalizedPullbackCoherence
