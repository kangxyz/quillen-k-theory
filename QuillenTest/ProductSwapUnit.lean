/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ProductSwapUnit

/-!
# Actual geometric swap unit regression

The whole-time geometric track and its literal original pullback map are audited together.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products
open Quillen.Waldhausen.IteratedS
open Quillen.PerfectComplexes Quillen.PerfectComplexes.ProductSwapUnit
universe u
namespace QuillenTest.ProductSwapUnit

/-- Regression keeps the original geometric spectrum pullback, rather than a substitute map. -/
theorem actual_pullback {S T : Scheme.{u}} (p : S ⟶ integerBase)
    (q : T ⟶ integerBase) (X : Scheme.{u}) :
    prespectrumMap (swapModelMap p q X) =
      boundedFlatPerfectPrespectrumMap (baseProductSwapMap p q X) :=
  swapModelMap_prespectrum p q X

#print axioms Quillen.PerfectComplexes.ProductSwapUnit.swap_unit
#print axioms Quillen.PerfectComplexes.ProductSwapUnit.swapModelMap_preserves
#print axioms Quillen.PerfectComplexes.ProductSwapUnit.unitTrack_square
#print axioms Quillen.PerfectComplexes.ProductSwapUnit.laurent_unitTrack_square
#print axioms actual_pullback

end QuillenTest.ProductSwapUnit
