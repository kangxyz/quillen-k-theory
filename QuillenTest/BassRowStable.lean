/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRowStable

/-! The actual stable roof retains its two loop coordinates and every signed degree. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.LoopPrespectrum
open Quillen.PerfectComplexes.CoefficientBassRowRefinement
open scoped Topology unitInterval
universe u
namespace QuillenTest.BassRowStable
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- Parameter looping retains the original cone structure and the independent row coordinate. -/
theorem parameterComparison_row (k : ℕ)
    (γ : Path ((source P a).point (k + 1)) ((source P a).point (k + 1)))
    (r s : unitInterval) :
    Path.toContinuousMap
      (Path.toContinuousMap ((parameterLoopingMap (comparison P a)).map (k + 1) γ) r) s =
        (source P a).structureMap (k + 1) (γ r) s := rfl

/-- The genuine parameter-looped roof arrow yields its original signed stable-group isomorphism.
-/
def roofIso (d : ℤ) :
    (stableHomotopyFunctor d).obj (parameterLooping (source P a)) ≅
      (stableHomotopyFunctor d).obj (parameterLooping (carrier P a)) :=
  @asIso _ _ _ _ ((stableHomotopyFunctor d).map (parameterLoopingMap (comparison P a)))
    (parameterComparison_isStableEquivalence P a d)

/-- The isomorphism does not choose a different forward representative. -/
theorem roofIso_hom (d : ℤ) :
    (roofIso P a d).hom =
      (stableHomotopyFunctor d).map (parameterLoopingMap (comparison P a)) := rfl

end QuillenTest.BassRowStable
