/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputIdentityMap

/-! Whole original raw map identity, unchanged Laurent inclusion, seed, and independent times. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalRawBass
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace QuillenTest.GlobalRawBassInputIdentityMap
variable (X : Scheme.{u})

/-- The whole identity starts at the unchanged raw map and ends at every original loop point. -/
theorem whole_endpoints (n : ℕ) (γ : (step X).space n) :
    (InputIdentity.mapHomotopy X).level n (0, γ) = (map (𝟙 X)).map n γ ∧
      (InputIdentity.mapHomotopy X).level n (1, γ) = γ :=
  ⟨(InputIdentity.mapHomotopy X).at_zero n γ, (InputIdentity.mapHomotopy X).at_one n γ⟩

/-- Homotopy, loop, and structure times are independent on every original raw loop. -/
theorem three_independent_times (n : ℕ) (r s z : unitInterval) (γ : (step X).space n) :
    Path.toContinuousMap ((InputIdentity.mapHomotopy X).level (n + 1)
      (r, (step X).structureMap n γ z)) s =
    Path.toContinuousMap ((step X).structureMap n
      ((InputIdentity.mapHomotopy X).level n (r, γ)) z) s :=
  congrArg (fun p ↦ Path.toContinuousMap p s) ((InputIdentity.mapHomotopy X).comm n r γ z)

/-- The original Laurent inclusion uses the actual original unit track at every homotopy time. -/
theorem original_inclusion (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (laurent.obj X))).space n) :
    (InputIdentity.coneHomotopy X).level n (r, (mappingConeInclusion (comparison X)).map n x) =
      (mappingConeInclusion (comparison X)).map n
        ((InputIdentity.laurentHomotopy X).level n (r, x)) :=
  InputIdentity.coneHomotopy_inclusion X n r x

/-- The original seed keeps its entire original unit loop and both specified source-null legs. -/
theorem original_seed (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen X)).space n) :
    Path.toContinuousMap ((InputIdentity.mapHomotopy X).level n
      (r, (transition X).map n x)) s =
      (InputIdentity.coneHomotopy X).level n
        (r, (((unitHomotopy X).postcomp (mappingConeInclusion (comparison X))).conjugateToZero
          (sourceNull X)).level n (s, x)) :=
  InputIdentity.mapHomotopy_transition_apply X n r s x

end QuillenTest.GlobalRawBassInputIdentityMap
