/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Covering.ChosenLift

/-! # Exact chosen-cover lift and original-topology regression tests -/
@[expose] public section
noncomputable section
universe u v
namespace QuillenTest.ChosenCoverCore
open Quillen

variable {T X U Y : Type u}
  [TopologicalSpace T] [TopologicalSpace X] [TopologicalSpace U] [TopologicalSpace Y]
  [LocallyPathConnectedSpace X] [SimplyConnectedSpace T]
  {p : T → X} {q : U → Y} (hp : IsCoveringMap p) (hq : IsCoveringMap q)
  (f : C(X, Y)) (t₀ : T) (u₀ : U) (h₀ : q u₀ = f (p t₀))

/-- The selected lift fixes the prescribed point, without replacing its fiber. -/
theorem prescribed_point : Covering.basedLift hp hq f t₀ u₀ h₀ t₀ = u₀ :=
  Covering.basedLift_point hp hq f t₀ u₀ h₀

/-- The entire original projection square is an equality of functions. -/
theorem projection_square : q ∘ Covering.basedLift hp hq f t₀ u₀ h₀ = f ∘ p := by
  funext t
  exact Covering.basedLift_projection hp hq f t₀ u₀ h₀ t

/-- Every other continuous lift with that point equals the actual chosen map. -/
theorem prescribed_lift_unique (k : C(T, U)) (hk : k t₀ = u₀)
    (hsq : q ∘ k = f ∘ p) : k = Covering.basedLift hp hq f t₀ u₀ h₀ :=
  Covering.eq_basedLift hp hq f t₀ u₀ h₀ k hk hsq

/-- Local charts prove LPC even with independent total and base universes. -/
theorem covering_topology_lpc {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B] [LocallyPathConnectedSpace B]
    {r : E → B} (hr : IsCoveringMap r) : LocallyPathConnectedSpace E :=
  Covering.locallyPathConnectedSpace_total hr

end QuillenTest.ChosenCoverCore
