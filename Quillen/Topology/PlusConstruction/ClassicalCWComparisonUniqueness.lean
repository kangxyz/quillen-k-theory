/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.Topology.DoubleMappingCylinder.HomotopyDescent
public import Quillen.Topology.PlusConstruction.DoubleCylinderChosenCovers
public import Quillen.Topology.DoubleMappingCylinder.CWWhitehead
/-!
# Ordinary classical-CW comparison uniqueness with explicitly supplied covers
The self-double-cylinder fold and C6 recognition give ordinary homotopy
cancellation on original maps. Actual covers and target-cover surjectivity remain
explicit until the local-cover construction supplies them; the commuting lift
is genuinely constructed. No cylinder
CW structure, realization, domination or prescribed-track coherence is assumed.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits MonoidalCategory Topology
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.IsPlusConstruction
open DoubleCylinder
variable {X₀ X₁ : Type u} [TopologicalSpace X₀] [TopologicalSpace X₁]
variable [T2Space X₀] [T2Space X₁]
variable (A : Set X₀) (B : Set X₁) [CWComplex A] [CWComplex B]
variable {D : TopCat.{u}}
/-- The original self-cylinder ends are homotopic because the actual fold is a
left inverse of the genuinely recognized left leg. -/
def classicalCWSelfEndHomotopyChosenCovers
    (f : TopCat.of A ⟶ TopCat.of B)
    {l : TopCat.of A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ B) ⟶ D}
    (sq : IsPushout (intervalEndpoints (TopCat.of A)) (endMap f f) l e)
    (a : A) (b : B) (γ : Path (f a) b) (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, u, u} f.hom γ N)
    {E G : Type u} [TopologicalSpace E] [TopologicalSpace G]
    [SimplyConnectedSpace E] [SimplyConnectedSpace G]
    {p : E → B} {d : G → D} (hp : IsCoveringMap p) (hd : IsCoveringMap d)
    (hdsurj : Function.Surjective d) (e₀ : E) :
      (gapLeftEndpoint (B := TopCat.of B)
        (C := TopCat.of B) e).Homotopy
      (gapRightEndpoint (B := TopCat.of B) (C := TopCat.of B) e) := by
  let := ClassicalCW.locallyPathConnectedSpace B
  let legEquiv := DoubleCylinder.cwHomotopyEquivOfWeakMap A B B f f sq B
      (gapLeftEndpoint (B := TopCat.of B) (C := TopCat.of B) e)
    (doubleCylinder_leftLeg_isWeakHomotopyEquivalence_chosenCovers
      f f sq a b b γ γ N hf hf hp hd hdsurj e₀)
  let q := selfFold f sq
  have hstart : q.comp (legEquiv.toFun.comp legEquiv.invFun) = legEquiv.invFun := by
    apply ContinuousMap.ext
    intro x
    exact ContinuousMap.congr_fun (selfFold_left f sq) (legEquiv.invFun x)
  let L : legEquiv.invFun.Homotopy q :=
    ((ContinuousMap.Homotopy.refl q).comp legEquiv.right_inv.some).cast hstart rfl
  let K : ((gapLeftEndpoint (B := TopCat.of B)
        (C := TopCat.of B) e).comp q).Homotopy (ContinuousMap.id D) :=
    ((ContinuousMap.Homotopy.refl
      (gapLeftEndpoint (B := TopCat.of B)
        (C := TopCat.of B) e)).comp L.symm).trans legEquiv.right_inv.some
  have hleft : ((gapLeftEndpoint (B := TopCat.of B) (C := TopCat.of B) e).comp q).comp
      (gapRightEndpoint (B := TopCat.of B) (C := TopCat.of B) e) =
      gapLeftEndpoint (B := TopCat.of B) (C := TopCat.of B) e := by
    apply ContinuousMap.ext
    intro x
    exact congrArg
      (gapLeftEndpoint (B := TopCat.of B)
        (C := TopCat.of B) e)
      (ContinuousMap.congr_fun (selfFold_right f sq) x)
  exact (K.compContinuousMap
      (gapRightEndpoint (B := TopCat.of B) (C := TopCat.of B) e)).cast hleft rfl
/-- The actual self-cylinder construction cancels precomposition with the
original plus map at the level of ordinary homotopies. -/
def classicalCWHomotopyCancelChosenCovers
    (f : TopCat.of A ⟶ TopCat.of B)
    {l : TopCat.of A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ B) ⟶ D}
    (sq : IsPushout (intervalEndpoints (TopCat.of A)) (endMap f f) l e)
    (a : A) (b : B) (γ : Path (f a) b) (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, u, u} f.hom γ N)
    {E G : Type u} [TopologicalSpace E] [TopologicalSpace G]
    [SimplyConnectedSpace E] [SimplyConnectedSpace G]
    {p : E → B} {d : G → D} (hp : IsCoveringMap p) (hd : IsCoveringMap d)
    (hdsurj : Function.Surjective d) (e₀ : E)
    {Y : Type u} [TopologicalSpace Y] (h₀ h₁ : C(B, Y))
    (H : (h₀.comp f.hom).Homotopy (h₁.comp f.hom)) : h₀.Homotopy h₁ := by
  let v := homotopyDesc f f sq h₀ h₁ H
  let L := classicalCWSelfEndHomotopyChosenCovers
    A B f sq a b γ N hf hp hd hdsurj e₀
  exact ((ContinuousMap.Homotopy.refl v).comp L).cast
    (homotopyDesc_left f f sq h₀ h₁ H) (homotopyDesc_right f f sq h₀ h₁ H)
/-- Two comparisons with supplied under-source homotopies are ordinarily
homotopic. No relative-under-source coherence of those supplied tracks is claimed. -/
def classicalCWComparisonHomotopyChosenCovers
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
    h₀.Homotopy h₁ :=
  classicalCWHomotopyCancelChosenCovers
    A B f sq a b γ N hf hp hd hdsurj e₀ h₀ h₁ (H₀.trans H₁.symm)
include A B in
/-- Ordinary homotopy uniqueness, with explicit geometric self-cylinder cover data
and no assumed cancellation or uniqueness certificate. -/
theorem homotopic_classicalCWComparisonsChosenCovers
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
  ⟨classicalCWComparisonHomotopyChosenCovers
    A B f sq a b γ N hf hp hd hdsurj e₀ g h₀ h₁ H₀ H₁⟩
end Quillen.IsPlusConstruction
