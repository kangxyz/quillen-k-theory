/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.PlusConstruction.RealizationComparisonExistence

/-! # Fresh tests of restricted actual comparison construction -/
@[expose] public section

open Quillen.DoubleCylinder

noncomputable section
open CategoryTheory Limits MonoidalCategory
open scoped Simplicial Topology unitInterval
universe u
namespace QuillenTest.N4RestrictedComparison

open Quillen
open DoubleCylinder
variable {A D : TopCat.{u}} {B C : SSet.{u}}

/-- The constructed comparison uses the actual inverse right leg and unchanged left leg. -/
theorem exactOriginalForward
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
    (IsPlusConstruction.comparisonEquivOfDominatedCylinder
      f g sq a b c γ δ N hf hg T r s Hdom hp hq hd ki kj hi hj e₀ f₀).toFun =
      (Realization.homotopyEquivOfWeakHomotopyEquivalenceOfDomination
      (gapRightEndpoint e)
      (IsPlusConstruction.doubleCylinder_rightLeg_isWeakHomotopyEquivalence_suppliedCovers
        f g sq a b c γ δ N hf hg hq hd kj hj f₀) T r s Hdom).invFun.comp (gapLeftEndpoint e) := rfl

/-- Both endpoints of the constructed under-source homotopy are actual original maps. -/
theorem actualUnderSourceEndpoints
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
    (hj : ∀ x, d (kj x) = gapRightEndpoint e (q x)) (e₀ : E) (f₀ : F) (x : A) :
    (IsPlusConstruction.comparisonUnderSourceHomotopyOfDominatedCylinder
      f g sq a b c γ δ N hf hg T r s Hdom hp hq hd ki kj hi hj e₀ f₀) (0, x) =
      (IsPlusConstruction.comparisonEquivOfDominatedCylinder
      f g sq a b c γ δ N hf hg T r s Hdom hp hq hd ki kj hi hj e₀ f₀).toFun (f x) ∧
    (IsPlusConstruction.comparisonUnderSourceHomotopyOfDominatedCylinder
      f g sq a b c γ δ N hf hg T r s Hdom hp hq hd ki kj hi hj e₀ f₀) (1, x) = g x :=
  ⟨(IsPlusConstruction.comparisonUnderSourceHomotopyOfDominatedCylinder
      f g sq a b c γ δ N hf hg T r s Hdom hp hq hd ki kj hi hj e₀ f₀).map_zero_left x,
    (IsPlusConstruction.comparisonUnderSourceHomotopyOfDominatedCylinder
      f g sq a b c γ δ N hf hg T r s Hdom hp hq hd ki kj hi hj e₀ f₀).map_one_left x⟩

/-- The base cylinder retains its complete original track at all times. -/
theorem fullOriginalTrack (f : A ⟶ |B|) (g : A ⟶ |C|)
    {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (|B| ⊕ |C|) ⟶ D}
    (sq : IsPushout (intervalEndpoints A) (endMap f g) l e) (t : unitInterval) (x : A) :
    endpointHomotopy f g sq (t, x) = l (x, ULift.up t) := rfl

end QuillenTest.N4RestrictedComparison
