/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Prespectrum.ConeHomotopySquareEquivalence
public import Quillen.Topology.Prespectrum.ConeStableNaturality

/-!
# Genuine stable excision for the unchanged whole-track cone map

The original full-track cone map factors literally through two original strict cone maps and
the original homotopy-arrow change. Genuine row excision makes the strict factors stable, while
the actual reverse-track homotopies make the middle factor a levelwise homotopy equivalence.
No levelwise inverse or Omega assumption is imposed on the supplied stable side maps.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Quillen.LoopPrespectrum
variable {E F E' F' : LoopPrespectrum.{u}}
  (f : E ⟶ F) (g : E' ⟶ F') (a : E ⟶ E') (b : F ⟶ F')
  (H : Homotopy (f ≫ b) (a ≫ g))

/-- Actual stable sides preserve the original whole-track cone map under genuine row excision. -/
theorem mappingConeSquareMap_isStableEquivalence_of_excision
    (hf : IsStableEquivalence (mappingConeFiberComparison f))
    (hfb : IsStableEquivalence (mappingConeFiberComparison (f ≫ b)))
    (hag : IsStableEquivalence (mappingConeFiberComparison (a ≫ g)))
    (hg : IsStableEquivalence (mappingConeFiberComparison g))
    (ha : IsStableEquivalence a) (hb : IsStableEquivalence b) :
    IsStableEquivalence (mappingConeSquareMap f g a b H) := by
  let sq₁ : Arrow.mk f ⟶ Arrow.mk (f ≫ b) := Arrow.homMk (𝟙 E) b (by simp)
  let sq₂ : Arrow.mk (a ≫ g) ⟶ Arrow.mk g := Arrow.homMk a (𝟙 F') (by simp)
  have h₁ := mappingConeMap_isStableEquivalence_of_excision sq₁ hf hfb
    (IsStableEquivalence.id E) hb
  have h₂ := mappingConeMap_isStableEquivalence_of_excision sq₂ hag hg ha
    (IsStableEquivalence.id F')
  have hH : IsStableEquivalence (mappingConeHomotopyMap H) :=
    isStableEquivalence_of_levelwise _ (mappingConeHomotopyMap_level_isWeakHomotopyEquivalence H)
  rw [mappingConeSquareMap_factor]
  exact h₁.comp (hH.comp h₂)

end Quillen.LoopPrespectrum
