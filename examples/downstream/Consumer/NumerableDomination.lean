/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Realization.ConnectorSimplexCone
public import Quillen.Topology.Realization.NumerableConnectorCover

/-! Independent clients construct actual extension and relative homotopy data.
They do not claim completion of the ordered-nerve domination argument. -/
@[expose] public section
noncomputable section
open Convexity
open scoped Topology unitInterval
universe u v
namespace Quillen.Consumer.NumerableDomination
open NumerableConnectorCover
variable {A : Type u} [TopologicalSpace A]

/-- A common convex carrier produces an actual continuous extension and its exact face equation. -/
theorem convex_simplex_extension (E : LocalEquiconnection A) {V : Set A}
    (hV : E.IsConvex V) (a : A) (ha : a ∈ V) {n : ℕ}
    (f : C(StdSimplex ℝ (Fin (n + 1)), A)) (hf : ∀ y, f y ∈ V) :
    ∃ g : C(StdSimplex ℝ (Fin (n + 2)), A),
      (∀ x, g x ∈ V) ∧ ∀ y, g (simplexBoundaryCone 0 y) = f y := by
  refine ⟨connectorCone E a f (fun y ↦ hV.pair_mem ha (hf y)),
    connectorCone_mem E hV a ha f hf, ?_⟩
  intro y
  rw [connectorCone_apply]
  simp only [unitInterval.symm_zero, E.connector_one]

/-- A connector-convex subset contracts to a chosen point through maps into that same subset,
with the chosen point stationary throughout. -/
def convex_subset_contraction (E : LocalEquiconnection A) {V : Set A}
    (hV : E.IsConvex V) (a : V) :
    (ContinuousMap.id V).HomotopyRel (ContinuousMap.const V a) {a} where
  toFun p := ⟨E.connector (⟨(p.2.1, a.1), hV.pair_mem p.2.2 a.2⟩, p.1),
    hV.connector_mem p.2.2 a.2 p.1⟩
  continuous_toFun := (E.connector.continuous.comp
    (((continuous_subtype_val.comp continuous_snd).prodMk continuous_const).subtype_mk _
      |>.prodMk continuous_fst)).subtype_mk _
  map_zero_left x := Subtype.ext (E.connector_zero ⟨(x.1, a.1), hV.pair_mem x.2 a.2⟩)
  map_one_left x := Subtype.ext (E.connector_one ⟨(x.1, a.1), hV.pair_mem x.2 a.2⟩)
  prop' t x hx := by
    have hxa : x = a := hx
    subst x
    exact Subtype.ext (E.connector_diagonal a.1 t)

end Quillen.Consumer.NumerableDomination
