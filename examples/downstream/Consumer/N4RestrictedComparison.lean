/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.PlusConstruction.RealizationComparisonExistence

/-! # Independent restricted comparison-existence client -/
@[expose] public section

open Quillen.DoubleCylinder

noncomputable section
open CategoryTheory Limits MonoidalCategory
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.Consumer.N4RestrictedComparison
open DoubleCylinder
variable {A D : TopCat.{u}} {B C : SSet.{u}}

/-- Actual maps are constructed under the explicitly retained realization,
domination and cover data. -/
theorem comparisonAndOriginalHomotopy
    (f : A ⟶ |B|) (g : A ⟶ |C|)
    {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (|B| ⊕ |C|) ⟶ D}
    (sq : IsPushout (intervalEndpoints A) (endMap f g) l e)
    (a : A) (b : |B|) (c : |C|) (γ : Path (f a) b) (δ : Path (g a) c)
    (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, u, u} f.hom γ N)
    (hg : IsPlusConstruction.{u, u, u} g.hom δ N)
    (T : SSet.{u}) (r : C(D, |T|)) (s : C(|T|, D))
    (Hdom : (s.comp r).Homotopy (ContinuousMap.id D))
    {E F G : Type u} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G]
    [SimplyConnectedSpace E] [SimplyConnectedSpace F] [SimplyConnectedSpace G]
    {p : E → |B|} {q : F → |C|} {d : G → D}
    (hp : IsCoveringMap p) (hq : IsCoveringMap q) (hd : IsCoveringMap d)
    (ki : C(E, G)) (kj : C(F, G))
    (hi : ∀ x, d (ki x) = gapLeftEndpoint e (p x))
    (hj : ∀ x, d (kj x) = gapRightEndpoint e (q x)) (e₀ : E) (f₀ : F) :
    ∃ h : ContinuousMap.HomotopyEquiv |B| |C|,
      Nonempty ((h.toFun.comp f.hom).Homotopy g.hom) :=
  IsPlusConstruction.exists_comparisonEquiv_of_dominatedCylinder
    f g sq a b c γ δ N hf hg T r s Hdom hp hq hd ki kj hi hj e₀ f₀

end Quillen.Consumer.N4RestrictedComparison
