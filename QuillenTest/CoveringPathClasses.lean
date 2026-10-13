/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Quillen.Topology.Covering.PathClasses

/-! Consumers of the actual endpoint identification for simply connected covers. -/

open Quillen

universe u v

noncomputable section

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
variable {p : E → B} (hp : IsCoveringMap p) [SimplyConnectedSpace E]

-- Two base paths have the same endpoint-fixed class exactly when their lifts end together.
example (e₀ : E) (x : B) (q r : Path.Homotopic.Quotient (p e₀) x) :
    hp.monodromy q ⟨e₀, rfl⟩ = hp.monodromy r ⟨e₀, rfl⟩ ↔ q = r :=
  (Covering.monodromy_basepoint_injective hp e₀ x).eq_iff

-- The fiber is inhabited exactly on the path component reached from the chosen point.
example (e₀ : E) (x : B) : Nonempty {e : E // p e = x} ↔ Joined (p e₀) x := by
  constructor
  · rintro ⟨e⟩
    exact ⟨((Covering.pathClassEquiv hp e₀ x).symm e).out⟩
  · rintro ⟨q⟩
    exact ⟨Covering.pathClassEquiv hp e₀ x (.mk q)⟩

-- Projection of a path to the displayed fiber point inverts lifted-endpoint transport.
example (e₀ : E) (x : B) (e : {e : E // p e = x}) :
    hp.monodromy ((Covering.pathClassEquiv hp e₀ x).symm e) ⟨e₀, rfl⟩ = e :=
  (Covering.pathClassEquiv hp e₀ x).apply_symm_apply e
