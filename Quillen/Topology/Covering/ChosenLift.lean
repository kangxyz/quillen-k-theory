/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Covering.LocallyPathConnected
public import Mathlib.Topology.Homotopy.Lifting

/-!
# Actual based maps between chosen covering spaces

Source-only draft. The source total is simply connected and is proved LPC
from its original covering charts and original LPC base. Pinned covering
lifting then constructs a continuous map with exact projection and point
equations. Global surjectivity is required separately only to select a target
fiber point when none has been supplied.
-/

@[expose] public section
noncomputable section
open scoped Topology
universe u
namespace Quillen.Covering

variable {T X U Y : Type u}
  [TopologicalSpace T] [TopologicalSpace X] [TopologicalSpace U] [TopologicalSpace Y]
  [LocallyPathConnectedSpace X] [SimplyConnectedSpace T]
  {p : T → X} {q : U → Y} (hp : IsCoveringMap p) (hq : IsCoveringMap q)
  (f : C(X, Y)) (t₀ : T) (u₀ : U) (h₀ : q u₀ = f (p t₀))

include hp hq h₀ in
/-- Existence and uniqueness retain the prescribed total-space point and exact projection map. -/
theorem existsUnique_basedLift :
    ∃! k : C(T, U), k t₀ = u₀ ∧ q ∘ k = f ∘ p := by
  let := locallyPathConnectedSpace_total hp
  exact hq.existsUnique_continuousMap_lifts (f.comp ⟨p, hp.continuous⟩) t₀ u₀ h₀

/-- The continuous based lift is chosen after its genuine existence and uniqueness are proved. -/
def basedLift : C(T, U) := (existsUnique_basedLift hp hq f t₀ u₀ h₀).choose

/-- The lift retains the prescribed original total-space point. -/
theorem basedLift_point : basedLift hp hq f t₀ u₀ h₀ t₀ = u₀ :=
  (existsUnique_basedLift hp hq f t₀ u₀ h₀).choose_spec.1.1

/-- The actual projection square commutes at every original total-space point. -/
theorem basedLift_projection (t : T) : q (basedLift hp hq f t₀ u₀ h₀ t) = f (p t) :=
  congr_fun (existsUnique_basedLift hp hq f t₀ u₀ h₀).choose_spec.1.2 t

/-- A continuous map with the same point and projection equations is the constructed based lift. -/
theorem eq_basedLift (k : C(T, U)) (hk : k t₀ = u₀) (hsq : q ∘ k = f ∘ p) :
    k = basedLift hp hq f t₀ u₀ h₀ :=
  (existsUnique_basedLift hp hq f t₀ u₀ h₀).choose_spec.2 k ⟨hk, hsq⟩

include hp hq t₀ in
/-- A surjective target cover supplies a fiber point and an actual commuting lift. -/
theorem exists_lift_of_surjective (hqsurj : Function.Surjective q) :
    ∃ k : C(T, U), ∀ t, q (k t) = f (p t) := by
  obtain ⟨u, hu⟩ := hqsurj (f (p t₀))
  exact ⟨basedLift hp hq f t₀ u hu, basedLift_projection hp hq f t₀ u hu⟩

end Quillen.Covering
