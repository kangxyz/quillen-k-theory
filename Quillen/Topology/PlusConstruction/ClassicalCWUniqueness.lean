/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.PlusConstruction.ClassicalCWComparison
public import Quillen.Topology.PlusConstruction.ClassicalCWComparisonUniqueness
public import Quillen.Topology.CWComplex.ThinNeighborhoods
public import Quillen.Topology.DoubleMappingCylinder.ThinNeighborhoods
public import Quillen.Topology.Covering.PathClassSimplyConnected

/-!
# Ordinary uniqueness of plus constructions on actual classical CW spaces

The double cylinder is the canonical original TopCat pushout. Its simply connected cover and those
of the original ends are the actual path-class totals with their chart topology.
No cover, domination, commuting lift or desired comparison is an input.

This leaf states the common-universe result. Transport of the stable coefficient
universe certificate is a separate adapter; no coefficient resizing is implicit.
-/
@[expose] public section
noncomputable section
open CategoryTheory Limits MonoidalCategory Topology
open scoped unitInterval
universe u
namespace Quillen.IsPlusConstruction
open DoubleCylinder
variable {X₀ X₁ X₂ : Type u}
variable [TopologicalSpace X₀] [TopologicalSpace X₁] [TopologicalSpace X₂]
variable [T2Space X₀] [T2Space X₁] [T2Space X₂]
variable (A : Set X₀) (B : Set X₁) (C : Set X₂)
variable [CWComplex A] [CWComplex B] [CWComplex C]

include A B C in
/-- Original same-universe plus maps between actual CW subtypes admit a genuine
comparison homotopy equivalence under the original source up to homotopy. -/
theorem exists_classicalCWComparison
    (f : TopCat.of A ⟶ TopCat.of B) (g : TopCat.of A ⟶ TopCat.of C)
    (a : A) (b : B) (c : C) (γ : Path (f a) b) (δ : Path (g a) c)
    (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, u, u} f.hom γ N)
    (hg : IsPlusConstruction.{u, u, u} g.hom δ N) :
    ∃ h : ContinuousMap.HomotopyEquiv B C, (h.toFun.comp f.hom).Homotopic g.hom := by
  let := ClassicalCW.locallyPathConnectedSpace A
  let := ClassicalCW.locallyPathConnectedSpace B
  let := ClassicalCW.locallyPathConnectedSpace C
  let := hf.targetPathConnected
  let := hg.targetPathConnected
  let D : TopCat.{u} := pushout (intervalEndpoints (TopCat.of A)) (endMap f g)
  let l : TopCat.of A ⊗ TopCat.I ⟶ D := pushout.inl _ _
  let e : TopCat.of (B ⊕ C) ⟶ D := pushout.inr _ _
  have sq : IsPushout (intervalEndpoints (TopCat.of A)) (endMap f g) l e :=
    IsPushout.of_hasPushout _ _
  let := DoubleCylinder.pathConnectedSpace f g sq a
  let := DoubleCylinder.locallyPathConnectedSpace f g sq
  let EB := ClassicalCW.pathThinNeighborhoods B
  let EC := ClassicalCW.pathThinNeighborhoods C
  let ED := DoubleCylinder.pathThinNeighborhoods f g sq EB EC
  let d₀ : D := gapLeftEndpoint (B := TopCat.of B) (C := TopCat.of C) e b
  let := (EB.prebundle b).totalSpaceTopology
  let := (EC.prebundle c).totalSpaceTopology
  let := (ED.prebundle d₀).totalSpaceTopology
  let := EB.total_simplyConnectedSpace b
  let := EC.total_simplyConnectedSpace c
  let := ED.total_simplyConnectedSpace d₀
  exact exists_classicalCWComparisonChosenCovers A B C f g sq a b c γ δ N hf hg
    (EB.isCoveringMap_projection b) (EC.isCoveringMap_projection c)
    (ED.isCoveringMap_projection d₀) (PathThinNeighborhoods.projection_surjective d₀)
    (PathThinNeighborhoods.totalBasepoint b) (PathThinNeighborhoods.totalBasepoint c)

omit [T2Space X₂] [CWComplex C] in
/-- The canonical self-cylinder gives ordinary cancellation into every same-universe
space, with the original precomposition map and no geometric data supplied. -/
def classicalCWHomotopyCancel
    (f : TopCat.of A ⟶ TopCat.of B)
    (a : A) (b : B) (γ : Path (f a) b) (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, u, u} f.hom γ N)
    {Y : Type u} [TopologicalSpace Y] (h₀ h₁ : C(B, Y))
    (H : (h₀.comp f.hom).Homotopy (h₁.comp f.hom)) : h₀.Homotopy h₁ := by
  let := ClassicalCW.locallyPathConnectedSpace A
  let := ClassicalCW.locallyPathConnectedSpace B
  let := hf.targetPathConnected
  let D : TopCat.{u} := pushout (intervalEndpoints (TopCat.of A)) (endMap f f)
  let l : TopCat.of A ⊗ TopCat.I ⟶ D := pushout.inl _ _
  let e : TopCat.of (B ⊕ B) ⟶ D := pushout.inr _ _
  have sq : IsPushout (intervalEndpoints (TopCat.of A)) (endMap f f) l e :=
    IsPushout.of_hasPushout _ _
  let := DoubleCylinder.pathConnectedSpace f f sq a
  let := DoubleCylinder.locallyPathConnectedSpace f f sq
  let EB := ClassicalCW.pathThinNeighborhoods B
  let ED := DoubleCylinder.pathThinNeighborhoods f f sq EB EB
  let d₀ : D := gapLeftEndpoint (B := TopCat.of B) (C := TopCat.of B) e b
  let := (EB.prebundle b).totalSpaceTopology
  let := (ED.prebundle d₀).totalSpaceTopology
  let := EB.total_simplyConnectedSpace b
  let := ED.total_simplyConnectedSpace d₀
  exact classicalCWHomotopyCancelChosenCovers A B f sq a b γ N hf
    (EB.isCoveringMap_projection b) (ED.isCoveringMap_projection d₀)
    (PathThinNeighborhoods.projection_surjective d₀)
    (PathThinNeighborhoods.totalBasepoint b) h₀ h₁ H

include A B in
omit [T2Space X₂] [CWComplex C] in
/-- Comparisons supplied only with original under-source homotopies are ordinarily
homotopic; no coherence of the prescribed under-source tracks is asserted. -/
theorem homotopic_classicalCWComparisons
    (f : TopCat.of A ⟶ TopCat.of B)
    (a : A) (b : B) (γ : Path (f a) b) (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, u, u} f.hom γ N)
    {Y : Type u} [TopologicalSpace Y] (g : C(A, Y)) (h₀ h₁ : C(B, Y))
    (H₀ : (h₀.comp f.hom).Homotopic g) (H₁ : (h₁.comp f.hom).Homotopic g) :
    h₀.Homotopic h₁ :=
  ⟨classicalCWHomotopyCancel A B f a b γ N hf h₀ h₁ (H₀.some.trans H₁.some.symm)⟩

include A B C in
/-- A genuine comparison equivalence exists, and every comparison under the original
source is ordinarily homotopic to it, for actual Hausdorff classical CW subtypes. -/
theorem classicalCWPlusUnique
    (f : TopCat.of A ⟶ TopCat.of B) (g : TopCat.of A ⟶ TopCat.of C)
    (a : A) (b : B) (c : C) (γ : Path (f a) b) (δ : Path (g a) c)
    (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, u, u} f.hom γ N)
    (hg : IsPlusConstruction.{u, u, u} g.hom δ N) :
    ∃ h : ContinuousMap.HomotopyEquiv B C,
      (h.toFun.comp f.hom).Homotopic g.hom ∧
        ∀ k : C(B, C), (k.comp f.hom).Homotopic g.hom → k.Homotopic h.toFun := by
  obtain ⟨h, H⟩ := exists_classicalCWComparison A B C f g a b c γ δ N hf hg
  exact ⟨h, H, fun k Hk ↦
    homotopic_classicalCWComparisons A B f a b γ N hf g.hom k h.toFun Hk H⟩

end Quillen.IsPlusConstruction
