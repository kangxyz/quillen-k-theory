/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyCofiber.UnreducedConeHomology
public import Quillen.Topology.LocalCoefficients.PointRelativeHomology
public import Quillen.Topology.LocalCoefficients.RelativeFiniteBoundary

/-! # Finite cone-chain bounds from the original map, with no homotopical conclusion assumed -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits Quillen.LocalCoefficients Quillen.ReducedMappingCone
open scoped Simplicial
universe u
namespace Consumer.UnreducedConeHomology
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- Every positive vertex-relative cycle in the original cone has a finite ambient boundary,
starting only from the original chain quasi-isomorphism. -/
theorem original_quasiIso_cone_finite_boundary (f : C(X, Y)) (V : ModuleCat.{u} ℤ)
    (hf : QuasiIso (pushforwardChainMap f (constant Y V))) (n : ℕ)
    (z : (relativeSingularChainComplex {unreducedVertex f}
      (constant (UnreducedSpace f) V)).cycles (n + 1)) :
    ∃ (s : Finset (SingularSimplex (UnreducedSpace f) ⦋n + 1 + 1⦌))
      (a : ∀ σ, simplexFiber (constant (UnreducedSpace f) V) σ),
      (relativeSingularChainComplex {unreducedVertex f} (constant (UnreducedSpace f) V)).d
        (n + 1 + 1) (n + 1)
        ((cokernel.π (pushforwardChainMap (subspaceInclusion {unreducedVertex f})
          (constant (UnreducedSpace f) V))).f (n + 1 + 1)
            (∑ σ ∈ s, chainInclusion (constant (UnreducedSpace f) V) σ (a σ))) =
        (relativeSingularChainComplex {unreducedVertex f}
          (constant (UnreducedSpace f) V)).iCycles (n + 1) z := by
  have hr := (unreducedCone_positive_homology_isZero_of_quasiIso f V hf n).of_iso
    (pointRelativeHomologyIso (unreducedVertex f) V n).symm
  apply relativeCycle_exists_finite_boundary
  have hz : (relativeSingularChainComplex {unreducedVertex f}
      (constant (UnreducedSpace f) V)).homologyπ (n + 1) = 0 := hr.eq_of_tgt _ _
  rw [hz]
  rfl

end Consumer.UnreducedConeHomology
