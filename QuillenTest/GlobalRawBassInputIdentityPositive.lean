/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputIdentityPositiveFactor
/-! Original seed and whole cone support, retaining all independent times. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalRawBass
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace QuillenTest.GlobalRawBassInputIdentityPositive
variable (X : Scheme.{u})

/-- Every original source-null value is preserved, with both original path halves. -/
theorem original_null (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen X)).space n) :
    (InputIdentityPositive.inclusion X).map n
      ((InputIdentityPositive.sourceNull X).level n (s, x)) =
        (sourceNull X).level n (s, x) :=
  DFunLike.congr_fun (InputIdentityPositive.sourceNull_factor X n) (s, x)

/-- The complete original seed, rather than just its endpoint, is the strict support image. -/
theorem original_seed : InputIdentityPositive.seed X ≫
    parameterLoopingMap (InputIdentityPositive.inclusion X) = transition X :=
  InputIdentityPositive.seed_factor X

/-- Every positive-cone point retains the fixed whole-cone identity, including its correction. -/
theorem whole_cone (n : ℕ) (r : unitInterval)
    (x : (mappingCone (InputIdentityPositive.chart X)).space n) :
    (InputIdentityPositive.inclusion X).map n
      ((InputIdentityPositive.coneHomotopy X).level n (r, x)) =
    (InputIdentity.coneHomotopy X).level n
      (r, (InputIdentityPositive.inclusion X).map n x) :=
  InputIdentityPositive.coneHomotopy_factor X n r x

/-- The actual fixed identity-on-seed face is recovered at independent homotopy and loop times. -/
theorem identity_seed (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen X)).space n) :
    (InputIdentityPositive.inclusion X).map n
      (Path.toContinuousMap ((InputIdentityPositive.mapHomotopy X).level n
        (r, (InputIdentityPositive.seed X).map n x)) s) =
    Path.toContinuousMap ((InputIdentity.mapHomotopy X).level n
      (r, (transition X).map n x)) s :=
  InputIdentityPositive.mapHomotopy_seed X n r s x

/-- Structure time stays independent of both actual positive identity and loop times. -/
theorem independent_structure (n : ℕ) (r s z : unitInterval)
    (γ : (parameterLooping (mappingCone (InputIdentityPositive.chart X))).space n) :
    Path.toContinuousMap ((InputIdentityPositive.mapHomotopy X).level (n + 1)
      (r, (parameterLooping (mappingCone (InputIdentityPositive.chart X))).structureMap n γ z)) s =
    Path.toContinuousMap
      ((parameterLooping (mappingCone (InputIdentityPositive.chart X))).structureMap n
        ((InputIdentityPositive.mapHomotopy X).level n (r, γ)) z) s :=
  congrArg (fun p ↦ Path.toContinuousMap p s)
    ((InputIdentityPositive.mapHomotopy X).comm n r γ z)

end QuillenTest.GlobalRawBassInputIdentityPositive
