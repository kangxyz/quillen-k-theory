/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.PlusConstruction.RealizationComparisonUniqueness

/-! # Independent ordinary homotopy-cancellation client -/
@[expose] public section

open Quillen.DoubleCylinder

noncomputable section
open CategoryTheory Limits MonoidalCategory
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.Consumer.N4RestrictedUniqueness
open DoubleCylinder
variable {A D : TopCat.{u}} {B : SSet.{u}}

/-- The supplied geometric inputs genuinely give ordinary cancellation on original maps. -/
theorem cancelOriginalPrecomposition
    (f : A ⟶ |B|)
    {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (|B| ⊕ |B|) ⟶ D}
    (sq : IsPushout (intervalEndpoints A) (endMap f f) l e)
    (a : A) (b : |B|) (γ : Path (f a) b) (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, u, u} f.hom γ N)
    (T : SSet.{u}) (r : C(D, |T|)) (s : C(|T|, D))
    (Hdom : (s.comp r).Homotopy (ContinuousMap.id D))
    {E G : Type u} [TopologicalSpace E] [TopologicalSpace G]
    [SimplyConnectedSpace E] [SimplyConnectedSpace G]
    {p : E → |B|} {d : G → D} (hp : IsCoveringMap p) (hd : IsCoveringMap d)
    (ki : C(E, G)) (hi : ∀ x, d (ki x) = gapLeftEndpoint e (p x)) (e₀ : E)
    {Y : Type u} [TopologicalSpace Y] (h₀ h₁ : C(|B|, Y))
    (H : (h₀.comp f.hom).Homotopy (h₁.comp f.hom)) : h₀.Homotopic h₁ :=
  ⟨IsPlusConstruction.homotopyCancelOfDominatedSelfCylinder
    f sq a b γ N hf T r s Hdom hp hd ki hi e₀ h₀ h₁ H⟩

end Quillen.Consumer.N4RestrictedUniqueness
