/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Covering.ChosenLift
public import Quillen.Topology.LocalCoefficients.TwistedWhiteheadSuppliedCovers

/-!
# Twisted homological Whitehead with constructed maps between chosen covers

Source-only draft. The actual covers remain supplied here, but their commuting
map is now constructed from simply connectedness, the source base's actual
LPC topology, and separate target-cover surjectivity. The coefficient and all
space universes are the same u, matching the proved regular-coefficient API.
-/

@[expose] public section
noncomputable section
open CategoryTheory
open scoped Topology
universe u
namespace Quillen.LocalCoefficients

variable {T X U Y : Type u}
  [TopologicalSpace T] [TopologicalSpace X] [TopologicalSpace U] [TopologicalSpace Y]
  [SimplyConnectedSpace T] [SimplyConnectedSpace U]
  [PathConnectedSpace X] [PathConnectedSpace Y] [LocallyPathConnectedSpace X]

/-- Actual chosen covers and their constructed lift prove weak equivalence of the original map. -/
theorem isWeakHomotopyEquivalence_of_twisted_quasiIso_chosenCovers
    {p : T → X} {q : U → Y} (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    (hqsurj : Function.Surjective q) (f : C(X, Y)) (t₀ : T)
    (hπ : Function.Bijective (piMap 0 f (x := p t₀) rfl))
    (hH : ∀ A : System.{u, u} Y, QuasiIso (UniverseLift.chainMap.{u, u, u} f A)) :
    IsWeakHomotopyEquivalence f := by
  obtain ⟨k, hk⟩ := Covering.exists_lift_of_surjective hp hq f t₀ hqsurj
  exact isWeakHomotopyEquivalence_of_twisted_quasiIso_suppliedCovers hp hq k f hk t₀ hπ hH

end Quillen.LocalCoefficients
