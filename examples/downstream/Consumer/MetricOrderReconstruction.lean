/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.MetricOrderComplex.RealizationReconstruction

/-!
# Coordinates faithfully detect actual compact-open paths

The unchanged continuous coordinate map acts pointwise on original realization
paths, with their existing compact-open topology. Global coordinate injectivity
makes this path map injective. No inverse path map or inverse continuity is
asserted. The final example allows the uncountable inclusion poset of sets of
real numbers.
-/

@[expose] public section
noncomputable section

open CategoryTheory Quillen Quillen.MetricOrderComplex
open scoped Simplicial Topology unitInterval

universe u

namespace Consumer.MetricOrderReconstruction

variable {P : Type u} [PartialOrder P] {x y : |nerve P|}

/-- Apply the actual coordinate map pointwise to a compact-open path. -/
def pathCoordinates :
    C(Path x y, Path (realizationCoordinates x) (realizationCoordinates y)) where
  toFun γ := γ.map realizationCoordinates.continuous
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun z : Path x y × I ↦ realizationCoordinates (z.1 z.2))
    fun_prop

/-- The actual path map is injective because its pointwise coordinate map is injective. -/
theorem pathCoordinates_injective : Function.Injective (pathCoordinates (x := x) (y := y)) := by
  intro γ δ h
  apply Path.ext
  funext t
  apply realizationCoordinates_injective
  exact congrArg (fun p : Path (realizationCoordinates x) (realizationCoordinates y) ↦ p t) h

/-- Equality of every barycentric coordinate at every time detects equality of original paths. -/
theorem paths_eq_of_weights (γ δ : Path x y)
    (h : ∀ t v, (realizationCoordinates (γ t)).weights v =
      (realizationCoordinates (δ t)).weights v) : γ = δ := by
  apply pathCoordinates_injective
  apply Path.ext
  funext t
  exact MetricOrderComplex.ext (h t)

example {x y : |nerve (Set ℝ)|} (γ δ : Path x y)
    (h : ∀ t A, (realizationCoordinates (γ t)).weights A =
      (realizationCoordinates (δ t)).weights A) : γ = δ :=
  paths_eq_of_weights γ δ h

end Consumer.MetricOrderReconstruction
