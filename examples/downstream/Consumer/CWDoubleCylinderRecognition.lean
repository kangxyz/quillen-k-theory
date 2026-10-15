/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.DoubleMappingCylinder.CWWhitehead

/-! # Independent actual-cylinder recognition clients -/
@[expose] public section

open Topology

open Quillen.DoubleCylinder

noncomputable section
open CategoryTheory Limits MonoidalCategory Set
universe u
namespace Quillen.Consumer.CWDoubleCylinderRecognition
open DoubleCylinder
variable {X₀ X₁ X₂ : Type u}
variable [TopologicalSpace X₀] [TopologicalSpace X₁] [TopologicalSpace X₂]
variable [T2Space X₀] [T2Space X₁] [T2Space X₂]
variable (A : Set X₀) (B : Set X₁) (C : Set X₂)
variable [CWComplex A] [CWComplex B] [CWComplex C]
variable {D : TopCat.{u}} (f : TopCat.of A ⟶ TopCat.of B) (g : TopCat.of A ⟶ TopCat.of C)
variable {l : TopCat.of A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
variable (sq : IsPushout (intervalEndpoints (TopCat.of A)) (endMap f g) l e)
variable {W : Type u} [TopologicalSpace W] [T2Space W]
variable (K : Set W) [CWComplex K] (k : C(K, D)) (hk : IsWeakHomotopyEquivalence k)

include A B C f g sq hk in
/-- An original weak map from an actual CW source has an actual two-sided inverse. -/
theorem originalWeakMapHasInverse : ∃ v : C(D, K),
    (v.comp k).Homotopic (ContinuousMap.id K) ∧
      (k.comp v).Homotopic (ContinuousMap.id D) :=
  ⟨cwWeakMapInverse A B C f g sq K k hk,
    ⟨cwWeakMapLeftHomotopy A B C f g sq K k hk⟩,
    ⟨cwWeakMapRightHomotopy A B C f g sq K k hk⟩⟩

include A B C f g sq in
/-- The exact original weak left leg is recognized without any CW structure on D. -/
theorem originalWeakLeftLeg
    (h : IsWeakHomotopyEquivalence
      (gapLeftEndpoint (B := TopCat.of B) (C := TopCat.of C) e)) :
    ∃ q : ContinuousMap.HomotopyEquiv B D,
      q.toFun = gapLeftEndpoint (B := TopCat.of B) (C := TopCat.of C) e :=
  ⟨cwLeftEndpointHomotopyEquiv A B C f g sq h, rfl⟩

end Quillen.Consumer.CWDoubleCylinderRecognition
