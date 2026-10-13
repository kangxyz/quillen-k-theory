/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Quillen.Topology.HomotopyGroups.Loop.NormalizedComponentProduct
import Quillen.Topology.Realization.OpenComponents

/-! # A separately configured client constructing the product from genuine domination -/

noncomputable section
open Quillen
open scoped Topology
universe u

-- The input gives domination maps, not a homotopy inverse for the desired product.
-- Their homotopy proves the label continuity needed for an actual whole-space equivalence.
example {X D A : Type u} [TopologicalSpace X] [TopologicalSpace D]
    [TopologicalSpace A] [DiscreteTopology A] (x : X)
    (a : C(Path x x, D)) (b : C(D, Path x x))
    (H : (b.comp a).Homotopy (ContinuousMap.id (Path x x)))
    (ho : ∀ d : D, IsOpen (pathComponent d))
    (label : Path x x → A) (a₀ : A) (r : A → Path x x)
    (hc : ∀ c γ, label γ = c ↔ Joined (r c) γ) (hr : r a₀ = Path.refl x) :
    ∃ e : ContinuousMap.HomotopyEquiv (A × pathComponent (Path.refl x)) (Path x x),
      (∀ z, e (a₀, z) = z.val) ∧ (∀ z, label (e z) = z.1) ∧
        ∀ γ, (e.invFun γ).1 = label γ := by
  let l : C(Path x x, A) := ⟨label, continuous_componentLabel_of_isOpen label r hc
    (fun c ↦ isOpen_pathComponent_of_domination a b H ho (r c))⟩
  refine ⟨normalizedLoopComponentProductEquiv l a₀ r hc hr, ?_, ?_, ?_⟩
  · exact normalizedLoopComponentProductMap_zero a₀ r
  · exact normalizedLoopComponentProductMap_label l a₀ r hc hr
  · exact normalizedLoopComponentProductEquiv_inverse_label l a₀ r hc hr

-- For an actual realization dominator, openness is proved instead of assumed.
example {X A : Type u} [TopologicalSpace X]
    [TopologicalSpace A] [DiscreteTopology A] (x : X) (T : SSet.{u})
    (a : C(Path x x, ↥(SSet.toTop.obj T))) (b : C(↥(SSet.toTop.obj T), Path x x))
    (H : (b.comp a).Homotopy (ContinuousMap.id (Path x x)))
    (label : Path x x → A) (a₀ : A) (r : A → Path x x)
    (hc : ∀ c γ, label γ = c ↔ Joined (r c) γ) (hr : r a₀ = Path.refl x) :
    Nonempty (ContinuousMap.HomotopyEquiv
      (A × pathComponent (Path.refl x)) (Path x x)) := by
  let l : C(Path x x, A) := ⟨label, continuous_componentLabel_of_isOpen label r hc
    (fun c ↦ realizationDominated_isOpen_pathComponent T a b H (r c))⟩
  exact ⟨normalizedLoopComponentProductEquiv l a₀ r hc hr⟩

-- A strict square of component labels is promoted using paths of actual representatives.
example {X Y A B : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace A] [DiscreteTopology A] [TopologicalSpace B] [DiscreteTopology B]
    {x : X} {y : Y} (f : C(X, Y)) (hf : f x = y) (k : A → B)
    (labelX : C(Path x x, A)) (labelY : C(Path y y, B))
    (r : A → Path x x) (s : B → Path y y)
    (hr : ∀ a, labelX (r a) = a)
    (hs : ∀ b γ, labelY γ = b ↔ Joined (s b) γ)
    (hk : ∀ γ, labelY (basedLoopMap f hf γ) = k (labelX γ)) :
    ((basedLoopMap f hf).comp (loopComponentProductMap r)).Homotopic
      ((loopComponentProductMap s).comp (loopComponentProductChange f hf k)) :=
  loopComponentProductMap_naturality_of_labels f hf k labelX labelY r s hr hs hk
