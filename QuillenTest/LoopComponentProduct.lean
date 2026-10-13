/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Quillen.Topology.HomotopyGroups.Loop.NormalizedComponentProduct

/-! # Actual inverse, unchanged labels, and the exactly normalized loop product -/

noncomputable section
open Quillen
open scoped Topology unitInterval
universe u

variable {X Y A B : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace A] [DiscreteTopology A] [TopologicalSpace B] [DiscreteTopology B]
  {x : X} {y : Y}

-- The product supplies an actual continuous inverse with both inverse homotopies and exact labels.
example (label : C(Path x x, A)) (a₀ : A) (r : A → Path x x)
    (h : ∀ a γ, label γ = a ↔ Joined (r a) γ) (hr : r a₀ = Path.refl x) :
    ∃ g : C(Path x x, A × pathComponent (Path.refl x)),
      (g.comp (normalizedLoopComponentProductMap a₀ r)).Homotopic
        (ContinuousMap.id _) ∧
      ((normalizedLoopComponentProductMap a₀ r).comp g).Homotopic
        (ContinuousMap.id _) ∧ ∀ γ, (g γ).1 = label γ := by
  let e := normalizedLoopComponentProductEquiv label a₀ r h hr
  exact ⟨e.invFun, e.left_inv, e.right_inv,
    normalizedLoopComponentProductEquiv_inverse_label label a₀ r h hr⟩

-- The original neutral-component inclusion is retained as an equality of maps.
example (label : C(Path x x, A)) (a₀ : A) (r : A → Path x x)
    (h : ∀ a γ, label γ = a ↔ Joined (r a) γ) (hr : r a₀ = Path.refl x) :
    (normalizedLoopComponentProductEquiv label a₀ r h hr).toFun.comp
      (⟨fun z ↦ (a₀, z), continuous_const.prodMk continuous_id⟩ :
        C(pathComponent (Path.refl x), A × pathComponent (Path.refl x))) =
          (⟨Subtype.val, continuous_subtype_val⟩ : C(pathComponent (Path.refl x), Path x x)) := by
  ext z t
  exact congrArg (fun γ : Path x x ↦ γ t)
    (normalizedLoopComponentProductMap_zero a₀ r z)

-- Independence is a displayed homotopy fixed on every point of the normalized slice.
example (a₀ : A) {r s : A → Path x x} (β : ∀ a, Path (r a) (s a)) :
    ∃ H : (normalizedLoopComponentProductMap a₀ r).Homotopy
        (normalizedLoopComponentProductMap a₀ s),
      ∀ t z, H (t, (a₀, z)) = z.val :=
  ⟨normalizedLoopComponentProductHomotopy a₀ β,
    normalizedLoopComponentProductHomotopy_zero a₀ β⟩

-- Naturality retains the actual loop, loop time, and representative-path time.
example (f : C(X, Y)) (h : f x = y) (k : A → B)
    (r : A → Path x x) (s : B → Path y y)
    (β : ∀ a, Path (basedLoopMap f h (r a)) (s (k a)))
    (a : A) (z : pathComponent (Path.refl x)) (t v : unitInterval) :
    loopComponentProductNaturality f h k r s β (t, (a, z)) v =
      ((basedLoopMap f h z.val).trans (β a t)) v := rfl
