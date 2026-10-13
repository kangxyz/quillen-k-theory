/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.Topology.PlusConstruction.ClassicalCWComparison
public import Quillen.Topology.PlusConstruction.ClassicalCWComparisonUniqueness
/-!
# Actual classical-CW comparison with explicitly supplied covers
C6 recognizes the original double-cylinder legs derived from the two original
plus certificates. This removes realization and cylinder-domination premises.
Actual simply connected covers, target-cover surjectivity and points remain
explicit. Their commuting lifts are constructed by the frozen chosen-cover API.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits MonoidalCategory Topology
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.Consumer.ClassicalCWPlus
open IsPlusConstruction
open DoubleCylinder
variable {X₀ X₁ X₂ : Type u}
variable [TopologicalSpace X₀] [TopologicalSpace X₁] [TopologicalSpace X₂]
variable [T2Space X₀] [T2Space X₁] [T2Space X₂]
variable (A : Set X₀) (B : Set X₁) (C : Set X₂)
variable [CWComplex A] [CWComplex B] [CWComplex C]
variable {D : TopCat.{u}}
include A B C in
/-- Original same-universe plus certificates give an actual CW comparison under the source. -/
theorem comparisonExists
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
    ∃ h : ContinuousMap.HomotopyEquiv B C, Nonempty ((h.toFun.comp f.hom).Homotopy g.hom) :=
  exists_classicalCWComparisonChosenCovers
    A B C f g sq a b c γ δ N hf hg hp hq hd hdsurj e₀ f₀
end Quillen.Consumer.ClassicalCWPlus
namespace Quillen.Consumer.ClassicalCWPlus
open IsPlusConstruction DoubleCylinder
variable {X₀ X₁ : Type u} [TopologicalSpace X₀] [TopologicalSpace X₁]
variable [T2Space X₀] [T2Space X₁]
variable (A : Set X₀) (B : Set X₁) [CWComplex A] [CWComplex B]
variable {D : TopCat.{u}}
include A B in
/-- Any two original comparisons under the source are ordinarily homotopic. -/
theorem ordinaryComparisonUniqueness
    (f : TopCat.of A ⟶ TopCat.of B)
    {l : TopCat.of A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ B) ⟶ D}
    (sq : IsPushout (intervalEndpoints (TopCat.of A)) (endMap f f) l e)
    (a : A) (b : B) (γ : Path (f a) b) (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, u, u} f.hom γ N)
    {E G : Type u} [TopologicalSpace E] [TopologicalSpace G]
    [SimplyConnectedSpace E] [SimplyConnectedSpace G]
    {p : E → B} {d : G → D} (hp : IsCoveringMap p) (hd : IsCoveringMap d)
    (hdsurj : Function.Surjective d) (e₀ : E)
    {Y : Type u} [TopologicalSpace Y] (g : C(A, Y)) (h₀ h₁ : C(B, Y))
    (H₀ : (h₀.comp f.hom).Homotopy g) (H₁ : (h₁.comp f.hom).Homotopy g) :
    h₀.Homotopic h₁ :=
  homotopic_classicalCWComparisonsChosenCovers
    A B f sq a b γ N hf hp hd hdsurj e₀ g h₀ h₁ H₀ H₁
end Quillen.Consumer.ClassicalCWPlus
