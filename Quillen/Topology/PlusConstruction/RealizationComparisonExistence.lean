/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.PlusConstruction.DoubleCylinderWeakEquivalence
public import Quillen.Topology.DoubleMappingCylinder.EndpointHomotopy
public import Quillen.Topology.Realization.Domination

/-!
# Restricted actual comparison existence for original plus constructions

The targets are actual simplicial realizations. The supplied actual double
cylinder has explicit maps to and from a realization with a retraction
homotopy. Supplied simply connected covers and actual commuting lifts are
retained. These geometric inputs give actual leg inverses, and their composite
constructs a comparison and its under-source homotopy. No comparison or
under-source homotopy is assumed. No general classical CW conclusion is made.
-/
@[expose] public section

open Quillen.DoubleCylinder

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits MonoidalCategory
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.IsPlusConstruction
open DoubleCylinder
variable {A D : TopCat.{u}} {B C : SSet.{u}}

/-- Construct an actual comparison equivalence from geometric cover and domination data,
without a supplied comparison map or a desired leg-equivalence certificate. -/
def comparisonEquivOfDominatedCylinder
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
    ContinuousMap.HomotopyEquiv |B| |C| :=
  (Realization.homotopyEquivOfWeakHomotopyEquivalenceOfDomination (gapLeftEndpoint e)
    (doubleCylinder_leftLeg_isWeakHomotopyEquivalence_suppliedCovers
      f g sq a b c γ δ N hf hg hp hd ki hi e₀) T r s Hdom).trans
    (Realization.homotopyEquivOfWeakHomotopyEquivalenceOfDomination (gapRightEndpoint e)
    (doubleCylinder_rightLeg_isWeakHomotopyEquivalence_suppliedCovers
      f g sq a b c γ δ N hf hg hq hd kj hj f₀) T r s Hdom).symm

/-- The comparison's under-source homotopy is constructed from the original full
cylinder and the actual right-leg inverse homotopy. -/
def comparisonUnderSourceHomotopyOfDominatedCylinder
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
    ((comparisonEquivOfDominatedCylinder
      f g sq a b c γ δ N hf hg T r s Hdom hp hq hd ki kj hi hj e₀ f₀).toFun.comp
        f.hom).Homotopy g.hom := by
  let J := Realization.homotopyEquivOfWeakHomotopyEquivalenceOfDomination (gapRightEndpoint e)
    (doubleCylinder_rightLeg_isWeakHomotopyEquivalence_suppliedCovers
      f g sq a b c γ δ N hf hg hq hd kj hj f₀) T r s Hdom
  let H := (ContinuousMap.Homotopy.refl J.invFun).comp (endpointHomotopy f g sq)
  exact (H.cast rfl rfl).trans
    ((J.left_inv.some.compContinuousMap g.hom).cast rfl rfl)

/-- Restricted existence: actual realization targets, supplied cover lifts and actual
cylinder domination yield a comparison equivalence under the original source. -/
theorem exists_comparisonEquiv_of_dominatedCylinder
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
    ∃ h : ContinuousMap.HomotopyEquiv |B| |C|, Nonempty ((h.toFun.comp f.hom).Homotopy g.hom) :=
  ⟨comparisonEquivOfDominatedCylinder
      f g sq a b c γ δ N hf hg T r s Hdom hp hq hd ki kj hi hj e₀ f₀,
    ⟨comparisonUnderSourceHomotopyOfDominatedCylinder
      f g sq a b c γ δ N hf hg T r s Hdom hp hq hd ki kj hi hj e₀ f₀⟩⟩

end Quillen.IsPlusConstruction
