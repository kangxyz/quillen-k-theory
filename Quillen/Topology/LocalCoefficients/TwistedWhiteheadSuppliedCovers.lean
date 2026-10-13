/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Covering.HomotopyGroups
public import Quillen.Topology.LocalCoefficients.CoveringHomologyComparison
public import Quillen.Topology.LocalCoefficients.HomologicalWhiteheadSimplyConnected

/-!
# Twisted homological Whitehead with supplied simply connected covers

The original twisted chain maps make the actual lift an integral homology
equivalence by the proved regular-coefficient Arrow isomorphism. The genuine
simply connected homological Whitehead theorem applies to that lift. Actual
covering projections descend its higher homotopy isomorphisms, and the supplied
Pi one isomorphism and connected bases finish complete weak equivalence of the
original base map, including Pi zero and all target components.

All covering spaces and the commuting lift are supplied geometric data.
No covering existence theorem or local implication from CW homotopy type is
assumed. The coefficient and all four space universes are the same u.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u

namespace Quillen.LocalCoefficients
variable {E B E' B' : Type u}
variable [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace E'] [TopologicalSpace B']
variable {p : E → B} {p' : E' → B'} (hp : IsCoveringMap p) (hp' : IsCoveringMap p')
variable [SimplyConnectedSpace E] [SimplyConnectedSpace E']
variable [PathConnectedSpace B]
variable (k : C(E, E')) (f : C(B, B')) (h : ∀ e, p' (k e) = f (p e))
variable (e₀ : E) (hπ : Function.Bijective (piMap 0 f (x := p e₀) rfl))

include hp hp' h e₀ hπ in
/-- The actual lift between the supplied simply connected total spaces is a
complete weak equivalence from the original all-local-system hypothesis. -/
theorem suppliedCoverLift_isWeakHomotopyEquivalence
    (hH : ∀ A : System.{u, u} B', QuasiIso (UniverseLift.chainMap.{u, u, u} f A)) :
    IsWeakHomotopyEquivalence k := by
  apply isWeakHomotopyEquivalence_of_integral_quasiIso k e₀
  exact covering_integral_quasiIso_of_all_localCoefficients hp hp' k f h e₀ hπ hH

variable [PathConnectedSpace B']

include hp hp' h e₀ hπ in
/-- The original base map is a complete weak equivalence. Its positive
homotopy groups and Pi zero are the existing ones, not a covering-space surrogate. -/
theorem isWeakHomotopyEquivalence_of_twisted_quasiIso_suppliedCovers
    (hH : ∀ A : System.{u, u} B', QuasiIso (UniverseLift.chainMap.{u, u, u} f A)) :
    IsWeakHomotopyEquivalence f := by
  have hk := suppliedCoverLift_isWeakHomotopyEquivalence hp hp' k f h e₀ hπ hH
  apply isWeakHomotopyEquivalence_of_connected f (p e₀)
  intro n
  cases n with
  | zero => exact hπ
  | succ m =>
    exact Covering.homotopyGroupMap_base_bijective hp hp' k f h e₀
      (by omega) (hk.homotopy_bijective e₀ (m + 2))

end Quillen.LocalCoefficients
