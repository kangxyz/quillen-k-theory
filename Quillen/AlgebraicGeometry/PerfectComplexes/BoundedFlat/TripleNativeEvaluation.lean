/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SplitTripleNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.RightFirstNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NormalizedMiddleNative
public import Quillen.Waldhausen.SConstruction.Iterated.ScalarTripleEvaluation

/-! Exact exported triple correspondence by the original scalar evaluation algebra. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.SplitTripleSimplex
variable {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)

/-- The full assembled evaluation is the exported native triple,
including every scalar parameter. -/
theorem comparison_native_evaluation (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen T)).space n) :
    prespectrumSimplexFamily (simplex f g h) n (comparisonParameter (r, s), x) =
      (boundedFlatTripleTrackComparison f g h).level n (r, (s, x)) := by
  unfold comparisonParameter boundedFlatTripleTrackComparison
  exact Quillen.scalar_triple_evaluation
    (E := originalPrespectrum (boundedFlatPerfectWaldhausen T))
    (F := originalPrespectrum (boundedFlatPerfectWaldhausen X))
    n (fun z x ↦ prespectrumSimplexFamily (simplex f g h) n (z, x))
    leftFirstParameter leftSecondParameter
    (normalizedLeftParameter.symm.trans normalizedRightParameter)
    rightFirstParameter rightSecondParameter
    (congrArg boundedFlatPerfectPrespectrumMap (Category.assoc f g h))
    (Category.assoc _ _ _).symm
    (boundedFlatNormalizedCompTrackComparison f (g ≫ h))
    ((boundedFlatNormalizedCompTrackComparison g h).postcomp (boundedFlatPerfectPrespectrumMap f))
    (boundedFlatNormalizedCompTrackComparison (f ≫ g) h)
    (Homotopy.RelHomotopy.precomp (boundedFlatPerfectPrespectrumMap h)
      (boundedFlatNormalizedCompTrackComparison f g))
    (boundedFlatNormalizedTripleTrackComparison f g h)
    (leftFirst_native f g h n) (leftSecond_native f g h n) (normalized_native f g h n)
    (rightFirst_native f g h n) (rightSecond_native f g h n) r s x

end Quillen.PerfectComplexes.SplitTripleSimplex
