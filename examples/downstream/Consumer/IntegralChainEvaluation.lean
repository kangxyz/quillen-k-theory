/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.SphericalRelativeCycle
public import Quillen.Topology.LocalCoefficients.StraightenedIntegralEvaluation
public import Quillen.Topology.LocalCoefficients.RelativeFiniteBoundary

/-! # Independent actual spherical-cycle to finite-boundary consumer -/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits Quillen Quillen.LocalCoefficients Convexity
open scoped Simplicial

universe u

variable {X : Type u} [TopologicalSpace X]

/-- Absolute homology vanishing produces a genuine finite relative boundary of
an arbitrary spherical representative, with its original lifted integer coefficients. -/
theorem downstream_spherical_finite_boundary (m : ℕ) (z : X) (f₀ : SphericalSimplex X z (m + 2))
    (hz : IsZero (homology (constant X integralCoefficientModule.{u}) (m + 2))) :
    ∃ (b : Finset (SingularSimplex X ⦋m + 3⦌)) (a : ∀ _τ, ULift.{u} ℤ),
      (relativeSingularChainComplex {z} (constant X integralCoefficientModule.{u})).d
        (m + 3) (m + 2)
        ((cokernel.π (pushforwardChainMap (subspaceInclusion {z})
          (constant X integralCoefficientModule.{u}))).f (m + 3)
          (∑ τ ∈ b, chainInclusion (constant X integralCoefficientModule.{u}) τ (a τ))) =
        sphericalRelativeChain f₀ := by
  have hr : IsZero ((relativeSingularChainComplex {z}
      (constant X integralCoefficientModule.{u})).homology (m + 2)) :=
    hz.of_iso (pointRelativeHomologyIso z integralCoefficientModule.{u} (m + 1)).symm
  have hπ : (relativeSingularChainComplex {z}
      (constant X integralCoefficientModule.{u})).homologyπ (m + 2) = 0 := hr.eq_of_tgt _ _
  have hc : (relativeSingularChainComplex {z}
      (constant X integralCoefficientModule.{u})).homologyπ (m + 2)
        (sphericalRelativeCycle f₀) = 0 := by
    rw [hπ]
    rfl
  obtain ⟨b, a, hb⟩ := relativeCycle_exists_finite_boundary {z}
    (constant X integralCoefficientModule.{u}) (m + 2) (sphericalRelativeCycle f₀) hc
  exact ⟨b, a, hb.trans (iCycles_sphericalRelativeCycle f₀)⟩
