/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.FirstObstruction

/-! Actual based-loop and spherical-map consumers of absolute first obstruction. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits Quillen.LocalCoefficients
universe u

namespace Quillen.Consumer.FirstObstruction
variable {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]

/-- Starting with mathlib's original integral singular homology, any two
actual based cubes admit an original whole-boundary-relative homotopy. -/
theorem original_based_cubes_homotopic (m : ℕ) (z : X)
    (hs : ∀ x : X, ∀ k : ℕ, 0 < k → k < m + 2 →
      Subsingleton (HomotopyGroup.Pi k X x))
    (hH : IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℤ)
      (m + 2)).obj integralCoefficientModule.{u}).obj (TopCat.of X)))
    (p q : GenLoop (Fin (m + 2)) X z) :
    p.val.HomotopicRel q.val (Cube.boundary (Fin (m + 2))) := by
  have hsub := subsingleton_pi_of_singularHomology_isZero m z hs hH
  have h : (Quotient.mk' p : HomotopyGroup.Pi (m + 2) X z) = Quotient.mk' q :=
    hsub.elim _ _
  exact Quotient.eq.mp h

/-- A displayed spherical singular simplex has an actual boundary-fixed
nullhomotopy, rather than only an equality in an auxiliary class model. -/
theorem original_spherical_nullhomotopy (m : ℕ) (z : X)
    (hs : ∀ x : X, ∀ k : ℕ, 0 < k → k < m + 2 →
      Subsingleton (HomotopyGroup.Pi k X x))
    (hH : IsZero (homology (constant X integralCoefficientModule.{u}) (m + 2)))
    (f₀ : SphericalSimplex X z (m + 2)) :
    Nonempty (f₀.val.HomotopyRel (ContinuousMap.const _ z) (simplexBoundary (m + 2))) :=
  spherical_nullhomotopic_of_homology_isZero m z f₀ hs hH

end Quillen.Consumer.FirstObstruction
