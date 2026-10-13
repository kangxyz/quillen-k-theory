/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas

/-! # Homeomorphisms of actual topological disjoint unions -/

@[expose] public section
universe u v w
namespace Homeomorph

/-- Homeomorphisms on the components induce the original componentwise sigma homeomorphism. -/
def sigmaCongrRight {ι : Type u} {X : ι → Type v} {Y : ι → Type w}
    [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
    (e : ∀ i, X i ≃ₜ Y i) : (Σ i, X i) ≃ₜ (Σ i, Y i) where
  toEquiv := Equiv.sigmaCongrRight fun i ↦ (e i).toEquiv
  continuous_toFun := continuous_sigma fun i ↦ continuous_sigmaMk.comp (e i).continuous
  continuous_invFun := continuous_sigma fun i ↦ continuous_sigmaMk.comp (e i).symm.continuous

end Homeomorph
