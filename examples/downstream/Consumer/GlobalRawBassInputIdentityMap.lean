/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputIdentityMap

/-! Independent consumption of the actual original global raw Bass map identity. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalRawBass
open scoped Topology unitInterval
universe u
namespace Consumer.GlobalRawBassInputIdentityMap

/-- The client supplies only the scheme, with no comparison square or higher filler hypothesis. -/
def originalMapIdentity (X : Scheme.{u}) : Homotopy (map (𝟙 X)) (𝟙 (step X)) :=
  InputIdentity.mapHomotopy X

/-- Every actual original loop point is recovered by the terminal whole identity map. -/
theorem whole_terminal (X : Scheme.{u}) (n : ℕ) (γ : (step X).space n) :
    (originalMapIdentity X).level n (1, γ) = γ :=
  (originalMapIdentity X).at_one n γ

end Consumer.GlobalRawBassInputIdentityMap
