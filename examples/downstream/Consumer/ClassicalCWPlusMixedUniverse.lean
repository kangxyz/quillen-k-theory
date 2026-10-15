/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.PlusConstruction.ClassicalCWUniquenessUniverseLift

/-! # Independent original successor-certificate and arbitrary-target consumers -/
@[expose] public section

open Topology

open Quillen.DoubleCylinder
open Quillen.IsPlusConstruction

noncomputable section
open CategoryTheory Limits MonoidalCategory
open scoped unitInterval
universe u w
namespace Quillen.Consumer.ClassicalCWPlusMixedUniverse
open IsPlusConstruction
open DoubleCylinder
variable {X₀ : Type u} {X₁ X₂ : Type (u + 1)}
variable [TopologicalSpace X₀] [TopologicalSpace X₁] [TopologicalSpace X₂]
variable [T2Space X₀] [T2Space X₁] [T2Space X₂]
variable (A : Set X₀) (B : Set X₁) (C : Set X₂)
variable [CWComplex A] [CWComplex B] [CWComplex C]

include A B C in
/-- The exact original u / u+1 / u+1 certificate gives equivalence and ordinary uniqueness. -/
theorem originalSuccessorCertificate
    (f : C(A, B)) (g : C(A, C))
    (a : A) (b : B) (c : C) (γ : Path (f a) b) (δ : Path (g a) c)
    (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, u + 1, u + 1} f γ N)
    (hg : IsPlusConstruction.{u, u + 1, u + 1} g δ N) :
    ∃ h : ContinuousMap.HomotopyEquiv B C,
      (h.toFun.comp f).Homotopic g ∧
        ∀ k : C(B, C), (k.comp f).Homotopic g → k.Homotopic h.toFun :=
  classicalCWPlusUnique_successor A B C f g a b c γ δ N hf hg

include A B in
omit [T2Space X₂] [CWComplex C] in
/-- Precomposition by the original plus map is injective on ordinary homotopy classes. -/
theorem ordinaryPrecompositionInjective
    (f : C(A, B))
    (a : A) (b : B) (γ : Path (f a) b) (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, u + 1, u + 1} f γ N)
    {Y : Type u} [TopologicalSpace Y] (h₀ h₁ : C(B, Y))
    (H : (h₀.comp f).Homotopic (h₁.comp f)) : h₀.Homotopic h₁ :=
  ⟨classicalCWHomotopyCancelCommonUniverse.{u, u + 1, u, 0} A B f a b γ N hf h₀ h₁ H.some⟩

end Quillen.Consumer.ClassicalCWPlusMixedUniverse
