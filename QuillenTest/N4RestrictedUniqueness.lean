/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.PlusConstruction.RealizationComparisonUniqueness

/-! # Fresh actual descent, self-fold and ordinary uniqueness regressions -/
@[expose] public section

open Quillen.DoubleCylinder

noncomputable section
open CategoryTheory Limits MonoidalCategory
open scoped Simplicial Topology unitInterval
universe u
namespace QuillenTest.N4RestrictedUniqueness

open Quillen
open DoubleCylinder
variable {A D : TopCat.{u}} {B : SSet.{u}}

/-- The final conclusion is ordinary homotopy of the original comparisons. -/
theorem ordinaryOriginalComparisonHomotopy
    (f : A ⟶ |B|)
    {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (|B| ⊕ |B|) ⟶ D}
    (sq : IsPushout (intervalEndpoints A) (endMap f f) l e)
    (a : A) (b : |B|) (γ : Path (f a) b) (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, u, u} f.hom γ N)
    (T : SSet.{u}) (r : C(D, |T|)) (s : C(|T|, D))
    (Hdom : (s.comp r).Homotopy (ContinuousMap.id D))
    {E G : Type u} [TopologicalSpace E] [TopologicalSpace G]
    [SimplyConnectedSpace E] [SimplyConnectedSpace G]
    {p : E → |B|} {d : G → D} (hp : IsCoveringMap p) (hd : IsCoveringMap d)
    (ki : C(E, G)) (hi : ∀ x, d (ki x) = gapLeftEndpoint e (p x)) (e₀ : E)
    {Y : Type u} [TopologicalSpace Y] (g : C(A, Y)) (h₀ h₁ : C(|B|, Y))
    (H₀ : (h₀.comp f.hom).Homotopy g) (H₁ : (h₁.comp f.hom).Homotopy g) : h₀.Homotopic h₁ :=
  IsPlusConstruction.homotopic_comparisons_of_dominatedSelfCylinder
    f sq a b γ N hf T r s Hdom hp hd ki hi e₀ g h₀ h₁ H₀ H₁

/-- The self-fold keeps both actual endpoint compositions equal to identity. -/
theorem actualSelfFoldBothEnds (f : A ⟶ |B|)
    {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (|B| ⊕ |B|) ⟶ D}
    (sq : IsPushout (intervalEndpoints A) (endMap f f) l e) :
    (selfFold f sq).comp (gapLeftEndpoint e) = ContinuousMap.id |B| ∧
      (selfFold f sq).comp (gapRightEndpoint e) = ContinuousMap.id |B| :=
  ⟨selfFold_left f sq, selfFold_right f sq⟩

/-- Descent keeps the complete supplied homotopy in the original cylinder. -/
theorem actualFullDescent (f : A ⟶ |B|)
    {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (|B| ⊕ |B|) ⟶ D}
    (sq : IsPushout (intervalEndpoints A) (endMap f f) l e)
    {Y : Type u} [TopologicalSpace Y] (h₀ h₁ : C(|B|, Y))
    (H : (h₀.comp f.hom).Homotopy (h₁.comp f.hom)) (t : unitInterval) (x : A) :
    homotopyDesc f f sq h₀ h₁ H (l (x, ULift.up t)) = H (t, x) :=
  homotopyDesc_apply_cylinder f f sq h₀ h₁ H t x

/-- Descent recovers both supplied maps, not only their homotopy classes. -/
theorem actualDescentBothEnds (f : A ⟶ |B|)
    {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (|B| ⊕ |B|) ⟶ D}
    (sq : IsPushout (intervalEndpoints A) (endMap f f) l e)
    {Y : Type u} [TopologicalSpace Y] (h₀ h₁ : C(|B|, Y))
    (H : (h₀.comp f.hom).Homotopy (h₁.comp f.hom)) :
    (homotopyDesc f f sq h₀ h₁ H).comp (gapLeftEndpoint e) = h₀ ∧
      (homotopyDesc f f sq h₀ h₁ H).comp (gapRightEndpoint e) = h₁ :=
  ⟨homotopyDesc_left f f sq h₀ h₁ H, homotopyDesc_right f f sq h₀ h₁ H⟩

end QuillenTest.N4RestrictedUniqueness
