/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.Topology.PlusConstruction.DoubleCylinderChosenCovers
public import Quillen.Topology.DoubleMappingCylinder.EndpointHomotopy
public import Quillen.Topology.DoubleMappingCylinder.CWWhitehead
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
namespace Quillen.IsPlusConstruction
open DoubleCylinder
variable {X₀ X₁ X₂ : Type u}
variable [TopologicalSpace X₀] [TopologicalSpace X₁] [TopologicalSpace X₂]
variable [T2Space X₀] [T2Space X₁] [T2Space X₂]
variable (A : Set X₀) (B : Set X₁) (C : Set X₂)
variable [CWComplex A] [CWComplex B] [CWComplex C]
variable {D : TopCat.{u}}
/-- Construct an actual comparison equivalence from explicit geometric covering data,
without a supplied comparison map or a desired leg-equivalence certificate. -/
def classicalCWComparisonEquivChosenCovers
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
    ContinuousMap.HomotopyEquiv B C := by
  let := ClassicalCW.locallyPathConnectedSpace B
  let := ClassicalCW.locallyPathConnectedSpace C
  exact (DoubleCylinder.cwHomotopyEquivOfWeakMap A B C f g sq B
      (gapLeftEndpoint (B := TopCat.of B) (C := TopCat.of C) e)
    (doubleCylinder_leftLeg_isWeakHomotopyEquivalence_chosenCovers
      f g sq a b c γ δ N hf hg hp hd hdsurj e₀)).trans
    (DoubleCylinder.cwHomotopyEquivOfWeakMap A B C f g sq C
      (gapRightEndpoint (B := TopCat.of B) (C := TopCat.of C) e)
    (doubleCylinder_rightLeg_isWeakHomotopyEquivalence_chosenCovers
      f g sq a b c γ δ N hf hg hq hd hdsurj f₀)).symm
/-- The comparison's under-source homotopy is constructed from the original full
cylinder and the actual right-leg inverse homotopy. -/
def classicalCWComparisonUnderSourceChosenCovers
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
    ((classicalCWComparisonEquivChosenCovers
      A B C f g sq a b c γ δ N hf hg hp hq hd hdsurj e₀ f₀).toFun.comp
        f.hom).Homotopy g.hom := by
  let := ClassicalCW.locallyPathConnectedSpace C
  let J := DoubleCylinder.cwHomotopyEquivOfWeakMap A B C f g sq C
      (gapRightEndpoint (B := TopCat.of B) (C := TopCat.of C) e)
    (doubleCylinder_rightLeg_isWeakHomotopyEquivalence_chosenCovers
      f g sq a b c γ δ N hf hg hq hd hdsurj f₀)
  let H := (ContinuousMap.Homotopy.refl J.invFun).comp (endpointHomotopy f g sq)
  exact (H.cast rfl rfl).trans
    ((J.left_inv.some.compContinuousMap g.hom).cast rfl rfl)
include A B C in
/-- Actual classical CW comparison existence with supplied covers and constructed lifts. -/
theorem exists_classicalCWComparisonChosenCovers
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
  ⟨classicalCWComparisonEquivChosenCovers
      A B C f g sq a b c γ δ N hf hg hp hq hd hdsurj e₀ f₀,
    ⟨classicalCWComparisonUnderSourceChosenCovers
      A B C f g sq a b c γ δ N hf hg hp hq hd hdsurj e₀ f₀⟩⟩
end Quillen.IsPlusConstruction
