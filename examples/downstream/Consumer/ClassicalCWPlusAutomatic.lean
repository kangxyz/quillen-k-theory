/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.PlusConstruction.ClassicalCWUniqueness

/-! # Independent no-cover classical-CW plus uniqueness consumer -/
@[expose] public section
noncomputable section
open CategoryTheory Limits MonoidalCategory Topology
open scoped unitInterval
universe u
namespace Quillen.Consumer.ClassicalCWPlusAutomatic
open IsPlusConstruction
open DoubleCylinder
variable {X₀ X₁ X₂ : Type u}
variable [TopologicalSpace X₀] [TopologicalSpace X₁] [TopologicalSpace X₂]
variable [T2Space X₀] [T2Space X₁] [T2Space X₂]
variable (A : Set X₀) (B : Set X₁) (C : Set X₂)
variable [CWComplex A] [CWComplex B] [CWComplex C]

include A B C in
/-- Actual two-model plus uniqueness, with the original paths, subgroup and maps retained. -/
theorem originalTwoModelUniqueness
    (f : TopCat.of A ⟶ TopCat.of B) (g : TopCat.of A ⟶ TopCat.of C)
    (a : A) (b : B) (c : C) (γ : Path (f a) b) (δ : Path (g a) c)
    (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, u, u} f.hom γ N)
    (hg : IsPlusConstruction.{u, u, u} g.hom δ N) :
    ∃ h : ContinuousMap.HomotopyEquiv B C,
      (h.toFun.comp f.hom).Homotopic g.hom ∧
        ∀ k : C(B, C), (k.comp f.hom).Homotopic g.hom → k.Homotopic h.toFun :=
  classicalCWPlusUnique A B C f g a b c γ δ N hf hg

include A B in
omit [T2Space X₂] [CWComplex C] in
/-- Precomposition by the original plus map is injective on ordinary homotopy classes. -/
theorem ordinaryPrecompositionInjective
    (f : TopCat.of A ⟶ TopCat.of B)
    (a : A) (b : B) (γ : Path (f a) b) (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, u, u} f.hom γ N)
    {Y : Type u} [TopologicalSpace Y] (h₀ h₁ : C(B, Y))
    (H : (h₀.comp f.hom).Homotopic (h₁.comp f.hom)) : h₀.Homotopic h₁ :=
  ⟨classicalCWHomotopyCancel A B f a b γ N hf h₀ h₁ H.some⟩

end Quillen.Consumer.ClassicalCWPlusAutomatic
