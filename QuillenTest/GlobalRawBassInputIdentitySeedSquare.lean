/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputIdentitySeedSquare

/-! Whole actual transition identity and its fixed original boundary choices. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalRawBass
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped unitInterval
universe u
namespace QuillenTest.GlobalRawBassInputIdentitySeedSquare
variable (X : Scheme.{u})
open CommonReferenceNerve InputIdentitySeedCarrier

/-- This is a whole square on the original input map, null, seed, and fixed map identity. -/
def originalSquare : (transitionInputHomotopy (𝟙 X)).Square
    (coneSquareIdentityTrack (transition X))
    (Homotopy.precomp (transition X) (InputIdentity.mapHomotopy X))
    ((boundedFlatPerfectPrespectrumIdHomotopy X).postcomp (transition X)) :=
  InputIdentitySeedSquare.square X

/-- Both whole homotopy boundaries keep their original selected transitions. -/
theorem original_routes (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen X)).space n) :
    (originalSquare X).level n (0, (s, x)) =
      (transitionInputHomotopy (𝟙 X)).level n (s, x) ∧
    (originalSquare X).level n (1, (s, x)) =
      (coneSquareIdentityTrack (transition X)).level n (s, x) :=
  ⟨(originalSquare X).at_zero n s x, (originalSquare X).at_one n s x⟩

/-- The moving left and right edges retain the fixed map and source identity homotopies. -/
theorem original_edges (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen X)).space n) :
    (originalSquare X).level n (r, (0, x)) =
      (InputIdentity.mapHomotopy X).level n (r, (transition X).map n x) ∧
    (originalSquare X).level n (r, (1, x)) =
      (transition X).map n ((boundedFlatPerfectPrespectrumIdHomotopy X).level n (r, x)) :=
  ⟨(originalSquare X).left n r x, (originalSquare X).right n r x⟩

/-- The whole basepoint line is fixed for both independent square coordinates. -/
theorem based_line (n : ℕ) (r s : unitInterval) :
    (originalSquare X).level n
      (r, (s, (originalPrespectrum (boundedFlatPerfectWaldhausen X)).point n)) =
      (step X).point n := (originalSquare X).at_point n r s

/-- Square time, input-comparison time, structure time, and loop time remain independent. -/
theorem independent_structure (n : ℕ) (r s t v : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen X)).space n) :
    Path.toContinuousMap ((originalSquare X).level (n + 1)
      (r, (s, (originalPrespectrum (boundedFlatPerfectWaldhausen X)).structureMap n x t))) v =
    Path.toContinuousMap ((step X).structureMap n
      ((originalSquare X).level n (r, (s, x))) t) v :=
  congrArg (fun p ↦ Path.toContinuousMap p v) ((originalSquare X).comm n r s x t)

/-- Each actual corrected null sheet uses the original identity correction and quotient clock. -/
theorem corrected_null (e : Bool) (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen X)).space n) :
    CutOpenCarrier.nativeEval (polyRef (𝟙 X)) (chart (X := X)) (laurentRef (𝟙 X))
      (ordinary (𝟙 X)) (shifted (𝟙 X)) n
        ((InputIdentitySeedMovingNull.correctedSquare X e).parameter (r, s)) x =
    (InputIdentityPositive.nullSquare X).level n
      (r, (s, (boundedFlatPerfectPrespectrumMap (projection.app X)).map n x)) :=
  InputIdentitySeedMovingNull.correctedSquare_native X e n r s x

/-- The actual six-face boundary keeps its two distinct carrier tips throughout. -/
theorem separate_tips : InputIdentitySeedCone.tip (𝟙 X) false ≠
    InputIdentitySeedCone.tip (𝟙 X) true := tips_distinct (𝟙 X)

/-- The whole carrier right route has the original two pasting cuts at every loop coordinate. -/
theorem right_route (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen X)).space n) :
    CutOpenCarrier.nativeEval (polyRef (𝟙 X)) (chart (X := X)) (laurentRef (𝟙 X))
      (ordinary (𝟙 X)) (shifted (𝟙 X)) n
        (InputIdentitySeedConjugateFaces.right X (r, s)) x =
    Path.toContinuousMap ((InputIdentitySeedConjugateFaces.nativeRight X).level n (r, x)) s :=
  InputIdentitySeedConjugateFaces.right_native X n r s x

end QuillenTest.GlobalRawBassInputIdentitySeedSquare
