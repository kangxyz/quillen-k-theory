/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Prespectrum.PushoutHomotopySquareEquivalence
public import Quillen.Topology.Prespectrum.PushoutStableEquivalence

/-!
# Stable preservation of the original whole-track reduced-pushout map

The existing mapOfHomotopies factors literally through two original strict span maps and two
actual arrow-change homotopy equivalences. Genuine row excision and the three original stable
corner maps therefore prove stability of that unchanged map. Both supplied whole leg tracks,
including their cylinder parametrization, are retained; neither square is made strict.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Quillen.LoopPrespectrum.HomotopyPushout
variable {A B C A' B' C' : LoopPrespectrum.{u}}
  (f : A ⟶ B) (g : A ⟶ C) (f' : A' ⟶ B') (g' : A' ⟶ C')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
  (Hf : Homotopy (f ≫ b) (a ≫ f')) (Hg : Homotopy (g ≫ c) (a ≫ g'))

/-- The exact whole-track pushout map is stable under genuine excision for its original rows. -/
theorem mapOfHomotopies_isStableEquivalence_of_excision
    (hA : ∀ n, Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (A.point (n + 1)))))
    (hB : ∀ n, Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (B.point (n + 1)))))
    (hC : ∀ n, Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (C.point (n + 1)))))
    (hA' : ∀ n, Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (A'.point (n + 1)))))
    (hB' : ∀ n, Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (B'.point (n + 1)))))
    (hC' : ∀ n, Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (C'.point (n + 1)))))
    (hf : IsStableEquivalence (mappingConeFiberComparison f))
    (hfb : IsStableEquivalence (mappingConeFiberComparison (f ≫ b)))
    (haf : IsStableEquivalence (mappingConeFiberComparison (a ≫ f')))
    (hf' : IsStableEquivalence (mappingConeFiberComparison f'))
    (hi : IsStableEquivalence (mappingConeFiberComparison (inr f g)))
    (hibc : IsStableEquivalence (mappingConeFiberComparison (inr (f ≫ b) (g ≫ c))))
    (hia : IsStableEquivalence (mappingConeFiberComparison (inr (a ≫ f') (a ≫ g'))))
    (hi' : IsStableEquivalence (mappingConeFiberComparison (inr f' g')))
    (ha : IsStableEquivalence a) (hb : IsStableEquivalence b) (hc : IsStableEquivalence c) :
    IsStableEquivalence (mapOfHomotopies f g f' g' a b c Hf Hg) := by
  have h₁ := map_isStableEquivalence_of_excision f g (f ≫ b) (g ≫ c) (𝟙 A) b c
    (by simp) (by simp) hA hB hC hA hB' hC' hf hfb hi hibc
    (IsStableEquivalence.id A) hb hc
  have h₂ := map_isStableEquivalence_of_excision (a ≫ f') (a ≫ g') f' g' a (𝟙 B') (𝟙 C')
    (by simp) (by simp) hA hB' hC' hA' hB' hC' haf hf' hia hi'
    ha (IsStableEquivalence.id B') (IsStableEquivalence.id C')
  have hL : IsStableEquivalence (leftHomotopyMap Hf (g ≫ c)) :=
    isStableEquivalence_of_levelwise _ (fun n ↦ isWeakHomotopyEquivalence_of_homotopyEquiv
      (leftHomotopyMapLevelEquiv Hf (g ≫ c) n))
  have hR : IsStableEquivalence (rightHomotopyMap (a ≫ f') Hg) :=
    isStableEquivalence_of_levelwise _ (fun n ↦ isWeakHomotopyEquivalence_of_homotopyEquiv
      (rightHomotopyMapLevelEquiv (a ≫ f') Hg n))
  rw [mapOfHomotopies_factor]
  exact h₁.comp (hL.comp (hR.comp h₂))

end Quillen.LoopPrespectrum.HomotopyPushout
