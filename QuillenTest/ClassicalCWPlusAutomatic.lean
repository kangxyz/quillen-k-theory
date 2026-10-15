/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.PlusConstruction.ClassicalCWUniqueness

/-! # Original-map regressions with no auxiliary geometric input -/
@[expose] public section

open Topology

open Quillen.DoubleCylinder
open Quillen.IsPlusConstruction

noncomputable section
open CategoryTheory Limits MonoidalCategory
open scoped unitInterval
universe u
namespace QuillenTest.ClassicalCWPlusAutomatic

open Quillen
open IsPlusConstruction
open DoubleCylinder
variable {X₀ X₁ X₂ : Type u}
variable [TopologicalSpace X₀] [TopologicalSpace X₁] [TopologicalSpace X₂]
variable [T2Space X₀] [T2Space X₁] [T2Space X₂]
variable (A : Set X₀) (B : Set X₁) (C : Set X₂)
variable [CWComplex A] [CWComplex B] [CWComplex C]

include A B C in
/-- Comparison existence consumes only the original CW data and original plus certificates. -/
theorem noAuxiliaryGeometryComparison
    (f : TopCat.of A ⟶ TopCat.of B) (g : TopCat.of A ⟶ TopCat.of C)
    (a : A) (b : B) (c : C) (γ : Path (f a) b) (δ : Path (g a) c)
    (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, u, u} f.hom γ N)
    (hg : IsPlusConstruction.{u, u, u} g.hom δ N) :
    ∃ h : ContinuousMap.HomotopyEquiv B C, (h.toFun.comp f.hom).Homotopic g.hom :=
  exists_classicalCWComparison A B C f g a b c γ δ N hf hg

include A B C in
/-- The constructed comparison is an equivalence, and every original comparison
is ordinarily homotopic to it. -/
theorem ordinaryUniqueEquivalence
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
/-- The ordinary comparison target need not carry CW, separation or connectedness assumptions. -/
theorem arbitraryTargetUniqueness
    (f : TopCat.of A ⟶ TopCat.of B)
    (a : A) (b : B) (γ : Path (f a) b) (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, u, u} f.hom γ N)
    {Y : Type u} [TopologicalSpace Y] (g : C(A, Y)) (h₀ h₁ : C(B, Y))
    (H₀ : (h₀.comp f.hom).Homotopic g) (H₁ : (h₁.comp f.hom).Homotopic g) :
    h₀.Homotopic h₁ :=
  homotopic_classicalCWComparisons A B f a b γ N hf g h₀ h₁ H₀ H₁

omit [T2Space X₂] [CWComplex C] in
/-- The actual cancellation homotopy starts and ends at the two original maps pointwise. -/
theorem actualCancellationEndpoints
    (f : TopCat.of A ⟶ TopCat.of B)
    (a : A) (b : B) (γ : Path (f a) b) (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, u, u} f.hom γ N)
    {Y : Type u} [TopologicalSpace Y] (h₀ h₁ : C(B, Y))
    (H : (h₀.comp f.hom).Homotopy (h₁.comp f.hom)) (x : B) :
    classicalCWHomotopyCancel A B f a b γ N hf h₀ h₁ H (0, x) = h₀ x ∧
      classicalCWHomotopyCancel A B f a b γ N hf h₀ h₁ H (1, x) = h₁ x :=
  ⟨(classicalCWHomotopyCancel A B f a b γ N hf h₀ h₁ H).map_zero_left x,
    (classicalCWHomotopyCancel A B f a b γ N hf h₀ h₁ H).map_one_left x⟩

end QuillenTest.ClassicalCWPlusAutomatic
