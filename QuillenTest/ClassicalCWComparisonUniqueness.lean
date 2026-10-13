/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.Topology.PlusConstruction.ClassicalCWComparisonUniqueness
/-! # Actual CW descent, self-fold and ordinary uniqueness regressions -/
@[expose] public section
noncomputable section
open CategoryTheory Limits MonoidalCategory Topology
open scoped Simplicial Topology unitInterval
universe u
namespace QuillenTest.ClassicalCWComparisonUniqueness

open Quillen
open DoubleCylinder
variable {X₀ X₁ : Type u} [TopologicalSpace X₀] [TopologicalSpace X₁]
variable [T2Space X₀] [T2Space X₁]
variable (A : Set X₀) (B : Set X₁) [CWComplex A] [CWComplex B]
variable {D : TopCat.{u}}
/-- The final conclusion is ordinary homotopy of the original comparisons. -/
theorem ordinaryOriginalComparisonHomotopy
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
  IsPlusConstruction.homotopic_classicalCWComparisonsChosenCovers
    A B f sq a b γ N hf hp hd hdsurj e₀ g h₀ h₁ H₀ H₁
omit [T2Space X₀] [T2Space X₁] [CWComplex A] [CWComplex B] in
/-- The self-fold keeps both actual endpoint compositions equal to identity. -/
theorem actualSelfFoldBothEnds (f : TopCat.of A ⟶ TopCat.of B)
    {l : TopCat.of A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ B) ⟶ D}
    (sq : IsPushout (intervalEndpoints (TopCat.of A)) (endMap f f) l e) :
    (selfFold f sq).comp
      (gapLeftEndpoint (B := TopCat.of B) (C := TopCat.of B) e) = ContinuousMap.id B ∧
      (selfFold f sq).comp
      (gapRightEndpoint (B := TopCat.of B) (C := TopCat.of B) e) = ContinuousMap.id B :=
  ⟨selfFold_left f sq, selfFold_right f sq⟩
omit [T2Space X₀] [T2Space X₁] [CWComplex A] [CWComplex B] in
/-- Descent keeps the complete supplied homotopy in the original cylinder. -/
theorem actualFullDescent (f : TopCat.of A ⟶ TopCat.of B)
    {l : TopCat.of A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ B) ⟶ D}
    (sq : IsPushout (intervalEndpoints (TopCat.of A)) (endMap f f) l e)
    {Y : Type u} [TopologicalSpace Y] (h₀ h₁ : C(B, Y))
    (H : (h₀.comp f.hom).Homotopy (h₁.comp f.hom)) (t : unitInterval) (x : A) :
    homotopyDesc f f sq h₀ h₁ H (l (x, ULift.up t)) = H (t, x) :=
  homotopyDesc_apply_cylinder f f sq h₀ h₁ H t x
omit [T2Space X₀] [T2Space X₁] [CWComplex A] [CWComplex B] in
/-- Descent recovers both supplied maps, not only their homotopy classes. -/
theorem actualDescentBothEnds (f : TopCat.of A ⟶ TopCat.of B)
    {l : TopCat.of A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ B) ⟶ D}
    (sq : IsPushout (intervalEndpoints (TopCat.of A)) (endMap f f) l e)
    {Y : Type u} [TopologicalSpace Y] (h₀ h₁ : C(B, Y))
    (H : (h₀.comp f.hom).Homotopy (h₁.comp f.hom)) :
    (homotopyDesc f f sq h₀ h₁ H).comp
      (gapLeftEndpoint (B := TopCat.of B) (C := TopCat.of B) e) = h₀ ∧
      (homotopyDesc f f sq h₀ h₁ H).comp
      (gapRightEndpoint (B := TopCat.of B) (C := TopCat.of B) e) = h₁ :=
  ⟨homotopyDesc_left f f sq h₀ h₁ H, homotopyDesc_right f f sq h₀ h₁ H⟩
end QuillenTest.ClassicalCWComparisonUniqueness
