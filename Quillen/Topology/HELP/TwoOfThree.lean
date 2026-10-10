/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.HELP.CancelFirst
public import Quillen.Topology.HELP.CancelSecond
public import Quillen.Topology.HELP.HomotopyInvariance
public import Quillen.Topology.HELP.Composition
public import Quillen.Topology.HELP.HomotopyEquiv

/-! # Compact HELP two-of-three and actual section comparisons

Both cancellation directions concern the original continuous maps. All
lifting properties retain the entire prescribed boundary homotopy. The
section corollaries use genuine strict identities or supplied homotopies
between actual composites, with no inverse family or fiber conclusion.
-/
@[expose] public section

noncomputable section
open scoped Topology
universe u
namespace Quillen
variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Two-of-three with the first map fixed. -/
theorem compactHELP_comp_iff_of_first {f : C(X, Y)} {g : C(Y, Z)}
    (hf : CompactHomotopyExtensionLiftingProperty f) :
    CompactHomotopyExtensionLiftingProperty (g.comp f) ↔
      CompactHomotopyExtensionLiftingProperty g :=
  ⟨fun h ↦ h.cancel_first hf, fun h ↦ h.comp hf⟩

/-- Two-of-three with the second map fixed. -/
theorem compactHELP_comp_iff_of_second {f : C(X, Y)} {g : C(Y, Z)}
    (hg : CompactHomotopyExtensionLiftingProperty g) :
    CompactHomotopyExtensionLiftingProperty (g.comp f) ↔
      CompactHomotopyExtensionLiftingProperty f :=
  ⟨fun h ↦ h.cancel_second hg, fun h ↦ hg.comp h⟩

/-- Every actual strict section of a compact HELP retraction has compact
HELP. No compactness of either whole space is required. -/
theorem compactHELP_section {p : C(Y, X)} {s : C(X, Y)}
    (hp : CompactHomotopyExtensionLiftingProperty p) (hps : p.comp s = ContinuousMap.id X) :
    CompactHomotopyExtensionLiftingProperty s := by
  have h : CompactHomotopyExtensionLiftingProperty (p.comp s) := by
    rw [hps]
    exact compactHELP_of_homotopyEquiv (ContinuousMap.HomotopyEquiv.refl X)
  exact h.cancel_second hp

/-- A transition carrying one actual compact HELP section to another has
compact HELP, for the unchanged transition map. -/
theorem compactHELP_transition {s₀ : C(X, Y)} {s₁ : C(X, Z)} {t : C(Y, Z)}
    (h₀ : CompactHomotopyExtensionLiftingProperty s₀)
    (h₁ : CompactHomotopyExtensionLiftingProperty s₁) (ht : t.comp s₀ = s₁) :
    CompactHomotopyExtensionLiftingProperty t := by
  have h : CompactHomotopyExtensionLiftingProperty (t.comp s₀) := ht.symm ▸ h₁
  exact h.cancel_first h₀

/-- The same transition conclusion holds for an actual homotopy-commuting
triangle, without changing the transition map. -/
theorem compactHELP_transition_of_homotopy {s₀ : C(X, Y)} {s₁ : C(X, Z)} {t : C(Y, Z)}
    (h₀ : CompactHomotopyExtensionLiftingProperty s₀)
    (h₁ : CompactHomotopyExtensionLiftingProperty s₁) (ht : (t.comp s₀).Homotopic s₁) :
    CompactHomotopyExtensionLiftingProperty t :=
  ((compactHELP_iff_of_homotopic ht).mpr h₁).cancel_first h₀

end Quillen
