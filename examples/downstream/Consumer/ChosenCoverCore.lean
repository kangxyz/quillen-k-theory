/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.TwistedWhiteheadChosenCovers

/-! # Independent clients for exact chosen-cover lifts in the common universe

The actual covers are supplied; their map is constructed. No categorical
realization, alternative base topology or inverse to a weak equivalence is assumed.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Consumer.ChosenCoverCore
open Quillen Quillen.LocalCoefficients

variable {T X U Y : Type u}
  [TopologicalSpace T] [TopologicalSpace X] [TopologicalSpace U] [TopologicalSpace Y]
  [SimplyConnectedSpace T] [SimplyConnectedSpace U]
  [PathConnectedSpace X] [PathConnectedSpace Y] [LocallyPathConnectedSpace X]
  {p : T → X} {q : U → Y} (hp : IsCoveringMap p) (hq : IsCoveringMap q)
  (f : C(X, Y)) (t₀ : T)
  (hπ : Function.Bijective (piMap 0 f (x := p t₀) rfl))
  (hH : ∀ A : System.{u, u} Y, QuasiIso (UniverseLift.chainMap.{u, u, u} f A))

include hp hq t₀ hπ hH

omit [PathConnectedSpace Y] in
/-- A prescribed fiber point gives an actual weak equivalence of cover totals. -/
theorem prescribed_lift_isWeak (u₀ : U) (h₀ : q u₀ = f (p t₀)) :
    IsWeakHomotopyEquivalence (Covering.basedLift hp hq f t₀ u₀ h₀) :=
  suppliedCoverLift_isWeakHomotopyEquivalence hp hq _ f
    (Covering.basedLift_projection hp hq f t₀ u₀ h₀) t₀ hπ hH

/-- A surjective target cover gives the exact lift and weak equivalence of the original base map. -/
theorem lift_and_original_base_are_weak (hqsurj : Function.Surjective q) :
    ∃ k : C(T, U), (∀ t, q (k t) = f (p t)) ∧
      IsWeakHomotopyEquivalence k ∧ IsWeakHomotopyEquivalence f := by
  obtain ⟨k, hk⟩ := Covering.exists_lift_of_surjective hp hq f t₀ hqsurj
  exact ⟨k, hk, suppliedCoverLift_isWeakHomotopyEquivalence hp hq k f hk t₀ hπ hH,
    isWeakHomotopyEquivalence_of_twisted_quasiIso_chosenCovers
      hp hq hqsurj f t₀ hπ hH⟩

end Consumer.ChosenCoverCore
