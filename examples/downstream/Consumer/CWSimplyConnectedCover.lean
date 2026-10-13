/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.CWComplex.SimplyConnectedCover

/-! # Independent consumer of a constructed universal covering -/

@[expose] public section
noncomputable section
open Set Topology Quillen.ClassicalCW
universe u
namespace Consumer.CWSimplyConnectedCover
variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable (C : Set X) [CWComplex C] [ConnectedSpace C]

/-- The constructed actual cover has a point over every original base point,
and any two upstairs paths with the same endpoints are genuinely homotopic. -/
theorem exists_cover_with_fibers_and_path_uniqueness :
    ∃ (E : Type u) (_ : TopologicalSpace E) (p : C(E, C)),
      IsCoveringMap p ∧ (∀ x : C, ∃ e : E, p e = x) ∧
        (∀ (e₀ e₁ : E) (a b : Path e₀ e₁), a.Homotopic b) := by
  obtain ⟨E, tE, p, hp, hs, hsc⟩ := exists_simplyConnected_cover C
  let := tE
  let := hsc
  exact ⟨E, tE, p, hp, hs, fun _ _ a b ↦ SimplyConnectedSpace.paths_homotopic a b⟩

end Consumer.CWSimplyConnectedCover
