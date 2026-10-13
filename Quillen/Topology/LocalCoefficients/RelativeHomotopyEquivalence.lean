/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.SmallChainExcision
public import Quillen.Topology.LocalCoefficients.HomotopyEquivalence

/-! # Vanishing of actual relative chains for homotopy-equivalent subspaces -/
@[expose] public section
noncomputable section
open CategoryTheory Limits
universe u
namespace Quillen.LocalCoefficients
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- The original spatial chain map of a homotopy equivalence is a quasi-isomorphism. -/
theorem pushforwardChainMap_quasiIso_of_homotopyEquiv
    (e : ContinuousMap.HomotopyEquiv X Y) (A : System.{u, u} Y) :
    QuasiIso (pushforwardChainMap e.toFun A) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact isIso_pushforwardHomologyMap_of_homotopyEquiv e A n

/-- The actual relative singular complex is acyclic when the original subspace
inclusion is the forward map of a homotopy equivalence. -/
theorem relativeSingularChainComplex_acyclic_of_homotopyEquiv
    (W : Set X) (A : System.{u, u} X) (e : ContinuousMap.HomotopyEquiv W X)
    (he : e.toFun = subspaceInclusion W) :
    (relativeSingularChainComplex W A).Acyclic := by
  have hq := pushforwardChainMap_quasiIso_of_homotopyEquiv e A
  rw [he] at hq
  let S : ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ) :=
    ShortComplex.mk (pushforwardChainMap (subspaceInclusion W) A)
      (cokernel.π _) (cokernel.condition _)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  exact hS.acyclic_X₃ hq

end Quillen.LocalCoefficients
