/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputIdentitySeedConjugation
/-! Whole actual raw seed carrier values and original chosen recipes. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalRawBass
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped unitInterval
universe u
namespace Consumer.GlobalRawBassInputIdentitySeedCarrier
variable {X Y : Scheme.{u}} (g : X ⟶ Y)
open InputIdentitySeedCarrier CommonReferenceNerve

/-- The original five-stage null comparison survives on both separate carrier sheets. -/
theorem original_null (e : Bool) (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).space n) :
    (InputIdentityPositive.inclusion X).map n
      (CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
        (ordinary g) (shifted g) n (InputIdentitySeedNull.pastedNull g e (r, s)) x) =
      (InputNull.originalNullComparison g).level n (r, (s, x)) :=
  InputIdentitySeedNull.originalNull_whole g e n r s x

/-- The full carrier conjugation is precisely the frozen raw transition homotopy. -/
theorem original_transition (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Y)).space n) :
    (InputIdentityPositive.inclusion X).map n
      (CutOpenCarrier.nativeEval (polyRef g) (chart (X := X)) (laurentRef g)
        (ordinary g) (shifted g) n (InputIdentitySeedConjugation.comparison g (r, s)) x) =
      Path.toContinuousMap ((transitionInputHomotopy g).level n (r, x)) s :=
  InputIdentitySeedConjugation.comparison_transition g n r s x

/-- The two sheet tips remain genuinely distinct before native evaluation. -/
theorem distinct_tips : InputIdentitySeedCone.tip g false ≠
    InputIdentitySeedCone.tip g true := InputIdentitySeedCarrier.tips_distinct g


end Consumer.GlobalRawBassInputIdentitySeedCarrier
