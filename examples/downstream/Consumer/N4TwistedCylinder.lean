/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.PlusConstruction.DoubleCylinderWeakEquivalence

/-! # Independent original twisted-cylinder weak-leg client with explicit covers -/
@[expose] public section

open Quillen.DoubleCylinder

noncomputable section
open CategoryTheory Limits MonoidalCategory
open scoped Topology unitInterval
universe u
namespace Quillen.Consumer.N4TwistedCylinder
open DoubleCylinder
variable {A B C D : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
variable {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
variable (sq : IsPushout (intervalEndpoints A) (endMap f g) l e)
include sq

/-- No leg equivalence or desired homology certificate is among the supplied inputs. -/
theorem originalWeakLegFromTwistedData
    (a : A) (b : B) (c : C) (γ : Path (f a) b) (δ : Path (g a) c)
    (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, u, u} f.hom γ N)
    (hg : IsPlusConstruction.{u, u, u} g.hom δ N)
    {E F : Type u} [TopologicalSpace E] [TopologicalSpace F]
    [SimplyConnectedSpace E] [SimplyConnectedSpace F]
    {p : E → B} {q : F → D} (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    (lift : C(E, F)) (hlift : ∀ x, q (lift x) = gapLeftEndpoint e (p x)) (e₀ : E) :
    IsWeakHomotopyEquivalence (gapLeftEndpoint e) :=
  IsPlusConstruction.doubleCylinder_leftLeg_isWeakHomotopyEquivalence_suppliedCovers
    f g sq a b c γ δ N hf hg hp hq lift hlift e₀

end Quillen.Consumer.N4TwistedCylinder
