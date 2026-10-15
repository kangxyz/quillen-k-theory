/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Realization.ConnectorSimplexCone
public import Quillen.Topology.Realization.MetricPointStarRefinement
public import Quillen.Topology.Realization.OrderedCoverNerve

/-! Named regressions for the bounded generic connector and numerable-cover primitives. -/
@[expose] public section

open Quillen.NumerableConnectorCover

noncomputable section
open Convexity
open scoped Topology unitInterval Simplicial
universe u v
namespace QuillenTest.NumerableDomination

open Quillen
open NumerableConnectorCover
variable {A : Type u} [TopologicalSpace A] {X : Type v} [TopologicalSpace X]

/-- The homotopy fixes every equal-value point, not just a distinguished basepoint. -/
theorem whole_equality_locus (E : LocalEquiconnection A) (f g : C(X, A))
    (h : ∀ x, (f x, g x) ∈ E.domain) (x : X) (hx : f x = g x) (t : I) :
    E.closeHomotopy f g h (t, x) = f x :=
  E.closeHomotopy_eq_of_eq f g h x hx t

/-- Relative endpoint control uses the actual original maps. -/
def relative_subset (E : LocalEquiconnection A) (f g : C(X, A))
    (h : ∀ x, (f x, g x) ∈ E.domain) (S : Set X) (hS : ∀ x ∈ S, f x = g x) :
    f.HomotopyRel g S := E.closeHomotopyRel f g h S hS

/-- The whole height-one cone fiber is collapsed, including in dimension one. -/
theorem edge_apex (E : LocalEquiconnection A) (a : A)
    (f : C(StdSimplex ℝ (Fin 1), A)) (h : ∀ y, (a, f y) ∈ E.domain)
    (y : StdSimplex ℝ (Fin 1)) : connectorCone E a f h (simplexBoundaryCone 1 y) = a := by
  rw [connectorCone_apply]
  simp only [unitInterval.symm_one, E.connector_zero]

/-- The opposite simplex face retains the original supplied map exactly. -/
theorem cone_opposite_face (E : LocalEquiconnection A) {n : ℕ} (a : A)
    (f : C(StdSimplex ℝ (Fin (n + 1)), A)) (h : ∀ y, (a, f y) ∈ E.domain)
    (y : StdSimplex ℝ (Fin (n + 1))) :
    connectorCone E a f h (simplexBoundaryCone 0 y) = f y := by
  rw [connectorCone_apply]
  simp only [unitInterval.symm_zero, E.connector_one]

/-- Local closed-support coordinates give a genuine nerve face, including zero coordinates. -/
theorem partition_local_simplex {ι : Type*} (ρ : PartitionOfUnity ι A)
    {W : ι → Set A} (hρ : ρ.IsSubordinate W) (x : A) :
    IsNerveFace W (ρ.fintsupport x) ∧
      chartDomain ρ (ρ.fintsupport x) ∈ 𝓝 x :=
  localNerveFace ρ hρ x

/-- Finite simplex charts retain each original partition coefficient. -/
theorem partition_chart_coordinate {ι : Type*} (ρ : PartitionOfUnity ι A)
    (s : Finset ι) (x : chartDomain ρ s) (i : s) :
    (finiteChart ρ s x).weights i = ρ i.1 x.1 := rfl

omit [TopologicalSpace A] in
/-- Every actual ordered-nerve simplex has the stated common intersection. -/
theorem ordered_simplex_common_point {ι : Type*} [LinearOrder ι] (W : ι → Set A)
    {n : SimplexCategoryᵒᵖ} (s : (orderedNerve W).toSSet.obj n) :
    ∃ x, ∀ j, x ∈ W (s.1.obj j) := orderedNerve_commonPoint W s

end QuillenTest.NumerableDomination
