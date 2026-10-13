/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.TwistedWhiteheadSuppliedCovers

/-! Actual component paths and original all-basepoint homotopy maps downstairs. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen.LocalCoefficients
universe u

namespace Quillen.Consumer.TwistedWhiteheadSuppliedCovers
variable {E B E' B' : Type u}
variable [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace E'] [TopologicalSpace B']
variable {p : E → B} {p' : E' → B'} (hp : IsCoveringMap p) (hp' : IsCoveringMap p')
variable [SimplyConnectedSpace E] [SimplyConnectedSpace E']
variable [PathConnectedSpace B] [PathConnectedSpace B']
variable (k : C(E, E')) (f : C(B, B')) (h : ∀ e, p' (k e) = f (p e))
variable (e₀ : E) (hπ : Function.Bijective (piMap 0 f (x := p e₀) rfl))
variable (hH : ∀ A : System.{u, u} B', QuasiIso (UniverseLift.chainMap.{u, u, u} f A))
include hp hp' h e₀ hπ hH

/-- The conclusion covers all target path components of the actual base map. -/
theorem originalComponentPaths (b' : B') : ∃ b : B, Nonempty (Path (f b) b') :=
  (isWeakHomotopyEquivalence_of_twisted_quasiIso_suppliedCovers
    hp hp' k f h e₀ hπ hH).component_surjective b'

/-- The actual homotopy map is bijective at every basepoint and every finite
homotopy-set degree, including zero. -/
theorem originalAllBasepoints (b : B) (n : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin n) f (x := b) rfl) :=
  (isWeakHomotopyEquivalence_of_twisted_quasiIso_suppliedCovers
    hp hp' k f h e₀ hπ hH).homotopy_bijective b n

end Quillen.Consumer.TwistedWhiteheadSuppliedCovers
