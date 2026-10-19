/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.Prespectrum.ParameterLooping
public import Quillen.Topology.HomotopyGroups.WeakEquivalence
public import Quillen.Topology.Prespectrum.FiniteStructureTransport

/-!
# Finite structure ranges under parameter-correct looping

The actual double-loop transpose is retained as a homeomorphism. Spectrum and loop
times are independent; no identification of their ordering is assumed.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Quillen.LoopPrespectrum

/-- The original parameter-loop structure gains its range from the next homotopy degree. -/
theorem parameterLooping_structure_bijective (E : LoopPrespectrum.{u}) (n j : ℕ)
    (hs : Function.Bijective (homotopyGroupMap (N := Fin (j + 1))
      (E.structureMap n) (E.map_point n))) :
    Function.Bijective (homotopyGroupMap (N := Fin j)
      ((parameterLooping E).structureMap n) ((parameterLooping E).map_point n)) := by
  have hl := homotopyGroupMap_basedLoopMap_bijective_of_succ
    (E.structureMap n) (E.map_point n) j hs
  have ht := homotopyGroupMap_bijective_of_homotopyEquiv
    (doubleLoopTransposeHomeomorph (E.point (n + 1))).toHomotopyEquiv
    (doubleLoopTranspose_refl _) j
  have h := ht.comp hl
  have hw : homotopyGroupMap (N := Fin j)
      ((parameterLooping E).structureMap n) ((parameterLooping E).map_point n) =
    homotopyGroupMap (N := Fin j) (doubleLoopTranspose (E.point (n + 1)))
      (doubleLoopTranspose_refl _) ∘
    homotopyGroupMap (N := Fin j) (basedLoopMap (E.structureMap n) (E.map_point n))
      (basedLoopMap_refl _ _) := by
    funext z
    exact homotopyGroupMap_comp _ (basedLoopMap_refl _ _)
      _ (doubleLoopTranspose_refl _) z
  rw [hw]
  exact h

end Quillen.LoopPrespectrum
