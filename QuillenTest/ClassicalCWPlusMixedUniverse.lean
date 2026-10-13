/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.PlusConstruction.ClassicalCWUniquenessUniverseLift

/-! # Original-map regressions across explicit coefficient universes -/
@[expose] public section
noncomputable section
open CategoryTheory Limits MonoidalCategory Topology
open scoped unitInterval
universe u v w z
namespace QuillenTest.ClassicalCWPlusMixedUniverse

open Quillen
open IsPlusConstruction
open DoubleCylinder
variable {X₀ : Type u} {X₁ : Type v} {X₂ : Type w}
variable [TopologicalSpace X₀] [TopologicalSpace X₁] [TopologicalSpace X₂]
variable [T2Space X₀] [T2Space X₁] [T2Space X₂]
variable (A : Set X₀) (B : Set X₁) (C : Set X₂)
variable [CWComplex A] [CWComplex B] [CWComplex C]

include A B C in
/-- Comparison existence consumes only the original CW data and original plus certificates. -/
theorem noAuxiliaryGeometryComparison
    (f : C(A, B)) (g : C(A, C))
    (a : A) (b : B) (c : C) (γ : Path (f a) b) (δ : Path (g a) c)
    (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, v, max u v w z} f γ N)
    (hg : IsPlusConstruction.{u, w, max u v w z} g δ N) :
    ∃ h : ContinuousMap.HomotopyEquiv B C, (h.toFun.comp f).Homotopic g :=
  exists_classicalCWComparison_commonUniverse A B C f g a b c γ δ N hf hg

include A B C in
/-- The constructed comparison is an equivalence, and every original comparison
is ordinarily homotopic to it. -/
theorem ordinaryUniqueEquivalence
    (f : C(A, B)) (g : C(A, C))
    (a : A) (b : B) (c : C) (γ : Path (f a) b) (δ : Path (g a) c)
    (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, v, max u v w z} f γ N)
    (hg : IsPlusConstruction.{u, w, max u v w z} g δ N) :
    ∃ h : ContinuousMap.HomotopyEquiv B C,
      (h.toFun.comp f).Homotopic g ∧
        ∀ k : C(B, C), (k.comp f).Homotopic g → k.Homotopic h.toFun :=
  classicalCWPlusUnique_commonUniverse A B C f g a b c γ δ N hf hg

include A B in
omit [T2Space X₂] [CWComplex C] in
/-- The ordinary comparison target need not carry CW, separation or connectedness assumptions. -/
theorem arbitraryTargetUniqueness
    (f : C(A, B))
    (a : A) (b : B) (γ : Path (f a) b) (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, v, max u v w z} f γ N)
    {Y : Type w} [TopologicalSpace Y] (g : C(A, Y)) (h₀ h₁ : C(B, Y))
    (H₀ : (h₀.comp f).Homotopic g) (H₁ : (h₁.comp f).Homotopic g) :
    h₀.Homotopic h₁ :=
  homotopic_classicalCWComparisons_commonUniverse A B f a b γ N hf g h₀ h₁ H₀ H₁

omit [T2Space X₂] [CWComplex C] in
/-- The actual cancellation homotopy starts and ends at the two original maps pointwise. -/
theorem actualCancellationEndpoints
    (f : C(A, B))
    (a : A) (b : B) (γ : Path (f a) b) (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, v, max u v w z} f γ N)
    {Y : Type w} [TopologicalSpace Y] (h₀ h₁ : C(B, Y))
    (H : (h₀.comp f).Homotopy (h₁.comp f)) (x : B) :
    classicalCWHomotopyCancelCommonUniverse A B f a b γ N hf h₀ h₁ H (0, x) = h₀ x ∧
      classicalCWHomotopyCancelCommonUniverse A B f a b γ N hf h₀ h₁ H (1, x) = h₁ x :=
  ⟨(classicalCWHomotopyCancelCommonUniverse A B f a b γ N hf h₀ h₁ H).map_zero_left x,
    (classicalCWHomotopyCancelCommonUniverse A B f a b γ N hf h₀ h₁ H).map_one_left x⟩


end QuillenTest.ClassicalCWPlusMixedUniverse

namespace QuillenTest.ClassicalCWPlusMixedUniverse

open Quillen
open PlusConstruction.UnivSubtype
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- Removing the exact whole-space wrappers gives the original spatial map by reflexivity. -/
theorem originalForward (f : C(X, Y)) :
    (down Y).comp ((map f).comp (up X)) = f := rfl

/-- The transported basepoint path retains every original time value. -/
theorem originalTrack (f : C(X, Y)) {x : X} {y : Y} (γ : Path (f x) y)
    (t : unitInterval) : liftPath f γ t = up Y (γ t) := rfl

/-- Nonabelian Pi-one transport uses the originally supplied track. -/
theorem originalBasedSquare (f : C(X, Y)) {x : X} {y : Y} (γ : Path (f x) y)
    (a : HomotopyGroup.Pi 1 X x) :
    basedPiOneMap (map f) (liftPath f γ) (piEquiv x a) =
      piEquiv y (basedPiOneMap f γ a) := basedPiOneMap_lift_apply f γ a

/-- The transported subgroup is the actual image of the original raw kernel. -/
theorem originalKernel (f : C(X, Y)) {x : X} {y : Y} (γ : Path (f x) y) :
    (basedPiOneMap (map f) (liftPath f γ)).ker = liftSubgroup (basedPiOneMap f γ).ker :=
  kernel_lift f γ

end QuillenTest.ClassicalCWPlusMixedUniverse
