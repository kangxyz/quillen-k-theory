/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.Topology.PlusConstruction.ClassicalCWComparison
/-! # Fresh tests of actual CW comparison with constructed covering lifts -/
@[expose] public section

open Topology

open Quillen.DoubleCylinder

noncomputable section
open CategoryTheory Limits MonoidalCategory
open scoped Simplicial Topology unitInterval
universe u
namespace QuillenTest.ClassicalCWComparison

open Quillen
open DoubleCylinder
variable {X₀ X₁ X₂ : Type u}
variable [TopologicalSpace X₀] [TopologicalSpace X₁] [TopologicalSpace X₂]
variable [T2Space X₀] [T2Space X₁] [T2Space X₂]
variable (A : Set X₀) (B : Set X₁) (C : Set X₂)
variable [CWComplex A] [CWComplex B] [CWComplex C]
variable {D : TopCat.{u}}
/-- The constructed comparison uses the actual inverse right leg and unchanged left leg. -/
theorem exactOriginalForward
    (f : TopCat.of A ⟶ TopCat.of B) (g : TopCat.of A ⟶ TopCat.of C)
    {l : TopCat.of A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
    (sq : IsPushout (intervalEndpoints (TopCat.of A)) (endMap f g) l e)
    (a : A) (b : B) (c : C) (γ : Path (f a) b) (δ : Path (g a) c)
    (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, u, u} f.hom γ N)
    (hg : IsPlusConstruction.{u, u, u} g.hom δ N)
    {E F G : Type u} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G]
    [SimplyConnectedSpace E] [SimplyConnectedSpace F] [SimplyConnectedSpace G]
    {p : E → B} {q : F → C} {d : G → D}
    (hp : IsCoveringMap p) (hq : IsCoveringMap q) (hd : IsCoveringMap d)
    (hdsurj : Function.Surjective d) (e₀ : E) (f₀ : F) :
    let _ := ClassicalCW.locallyPathConnectedSpace C
    (IsPlusConstruction.classicalCWComparisonEquivChosenCovers
      A B C f g sq a b c γ δ N hf hg hp hq hd hdsurj e₀ f₀).toFun =
      (DoubleCylinder.cwHomotopyEquivOfWeakMap A B C f g sq C
      (gapRightEndpoint (B := TopCat.of B) (C := TopCat.of C) e)
      (IsPlusConstruction.doubleCylinder_rightLeg_isWeakHomotopyEquivalence_chosenCovers
        f g sq a b c γ δ N hf hg hq hd hdsurj f₀)).invFun.comp
      (gapLeftEndpoint (B := TopCat.of B) (C := TopCat.of C) e) := rfl
/-- Both endpoints of the constructed under-source homotopy are actual original maps. -/
theorem actualUnderSourceEndpoints
    (f : TopCat.of A ⟶ TopCat.of B) (g : TopCat.of A ⟶ TopCat.of C)
    {l : TopCat.of A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
    (sq : IsPushout (intervalEndpoints (TopCat.of A)) (endMap f g) l e)
    (a : A) (b : B) (c : C) (γ : Path (f a) b) (δ : Path (g a) c)
    (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, u, u} f.hom γ N)
    (hg : IsPlusConstruction.{u, u, u} g.hom δ N)
    {E F G : Type u} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G]
    [SimplyConnectedSpace E] [SimplyConnectedSpace F] [SimplyConnectedSpace G]
    {p : E → B} {q : F → C} {d : G → D}
    (hp : IsCoveringMap p) (hq : IsCoveringMap q) (hd : IsCoveringMap d)
    (hdsurj : Function.Surjective d) (e₀ : E) (f₀ : F) (x : A) :
    (IsPlusConstruction.classicalCWComparisonUnderSourceChosenCovers
      A B C f g sq a b c γ δ N hf hg hp hq hd hdsurj e₀ f₀) (0, x) =
      (IsPlusConstruction.classicalCWComparisonEquivChosenCovers
      A B C f g sq a b c γ δ N hf hg hp hq hd hdsurj e₀ f₀).toFun (f x) ∧
    (IsPlusConstruction.classicalCWComparisonUnderSourceChosenCovers
      A B C f g sq a b c γ δ N hf hg hp hq hd hdsurj e₀ f₀) (1, x) = g x :=
  ⟨(IsPlusConstruction.classicalCWComparisonUnderSourceChosenCovers
      A B C f g sq a b c γ δ N hf hg hp hq hd hdsurj e₀ f₀).map_zero_left x,
    (IsPlusConstruction.classicalCWComparisonUnderSourceChosenCovers
      A B C f g sq a b c γ δ N hf hg hp hq hd hdsurj e₀ f₀).map_one_left x⟩
omit [T2Space X₀] [T2Space X₁] [T2Space X₂] [CWComplex A] [CWComplex B] [CWComplex C] in
/-- The base cylinder retains its complete original track at all times. -/
theorem fullOriginalTrack (f : TopCat.of A ⟶ TopCat.of B) (g : TopCat.of A ⟶ TopCat.of C)
    {l : TopCat.of A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
    (sq : IsPushout (intervalEndpoints (TopCat.of A)) (endMap f g) l e) (t : unitInterval) (x : A) :
    endpointHomotopy f g sq (t, x) = l (x, ULift.up t) := rfl
end QuillenTest.ClassicalCWComparison
