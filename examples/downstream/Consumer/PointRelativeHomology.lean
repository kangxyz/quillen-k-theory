/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.PointRelativeHomology
public import Quillen.Topology.LocalCoefficients.RelativeFiniteBoundary

/-! # A downstream finite boundary from actual ordinary homology vanishing -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits Quillen.LocalCoefficients
open scoped Simplicial
universe u
namespace Consumer.PointRelativeHomology
variable {X : Type u} [TopologicalSpace X]

/-- Zero ordinary positive homology yields a finite ambient bounding chain for any relative
cycle. -/
theorem ordinary_homology_zero_finite_boundary (x : X) (V : ModuleCat.{u} ℤ) (n : ℕ)
    (h : IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℤ)
      (n + 1)).obj V).obj (TopCat.of X)))
    (z : (relativeSingularChainComplex {x} (constant X V)).cycles (n + 1)) :
    ∃ (s : Finset (SingularSimplex X ⦋n + 1 + 1⦌))
      (a : ∀ σ, simplexFiber (constant X V) σ),
      (relativeSingularChainComplex {x} (constant X V)).d (n + 1 + 1) (n + 1)
        ((cokernel.π (pushforwardChainMap (subspaceInclusion {x}) (constant X V))).f
          (n + 1 + 1) (∑ σ ∈ s, chainInclusion (constant X V) σ (a σ))) =
        (relativeSingularChainComplex {x} (constant X V)).iCycles (n + 1) z := by
  have hr := h.of_iso (singularPointRelativeHomologyIso x V n).symm
  apply relativeCycle_exists_finite_boundary
  have hz : (relativeSingularChainComplex {x} (constant X V)).homologyπ (n + 1) = 0 :=
    hr.eq_of_tgt _ _
  rw [hz]
  rfl

end Consumer.PointRelativeHomology
