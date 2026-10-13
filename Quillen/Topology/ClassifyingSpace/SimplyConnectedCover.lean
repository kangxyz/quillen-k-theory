/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.MetricOrderComplex.RealizationCover
public import Quillen.Topology.ClassifyingSpace.PosetLoop

/-!
# Constructed simply connected covers of original categorical realizations

The actual universal poset-resolution equivalence
and actual weak-to-metric order equivalence provide the pullback parameter.
Object and morphism universes remain independent. This does not convert an
arbitrary classical CW space or arbitrary simplicial realization into a nerve.
-/

@[expose] public section
noncomputable section
open CategoryTheory
open scoped Topology
universe u v
namespace Quillen.RankedChainOrder

variable (C : Type u) [Category.{v} C] [PathConnectedSpace (ClassifyingSpace C)]

/-- The actual original categorical realization has a constructed simply connected cover. -/
theorem exists_simplyConnected_classifying_cover (c : C) :
    ∃ T : Type (max u v), ∃ t : TopologicalSpace T,
      letI := t
      ∃ q : C(T, ClassifyingSpace C),
        IsCoveringMap q ∧ Function.Surjective q ∧ SimplyConnectedSpace T :=
  Covering.exists_simplyConnected_cover_of_localEquiconnection
    ((universalResolutionHomotopyEquiv C).symm.trans
      (MetricOrderComplex.realizationHomotopyEquiv
        (P := ResolutionPoset (AsSmall.{0} C))))
    MetricOrderComplex.localEquiconnection (classifyingSpacePoint c)

end Quillen.RankedChainOrder
