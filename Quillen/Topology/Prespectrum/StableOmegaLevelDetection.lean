/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.StableOmegaBasedDetection
public import Quillen.Topology.HomotopyGroups.Loop.BasedDetection
public import Quillen.Topology.HomotopyGroups.WeakEquivalenceCancellation

/-!
# Complete level detection of stable equivalences between Omega-prespectra

An original strict map between genuine Omega-prespectra is a stable equivalence exactly when
its original map at every level is a complete weak homotopy equivalence. All source components
and target component coverage are retained. The proof uses signed stable detection at chosen
points, natural loop-component translation, and the original structure square. No separation,
connectedness, basepoint cofibration, or cone-preservation hypothesis is used.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace Quillen.LoopPrespectrum

variable {E F : LoopPrespectrum.{u}} (hE : E.IsOmega) (hF : F.IsOmega) (f : E ⟶ F)
include hE hF

/-- A stable equivalence between genuine Omega-prespectra is completely weak at every original
level, including every source point and every target component. -/
theorem level_isWeakHomotopyEquivalence_of_isStableEquivalence (hf : IsStableEquivalence f)
    (k : ℕ) : IsWeakHomotopyEquivalence (f.map k) := by
  have hl := basedLoopMap_isWeakHomotopyEquivalence_of_bijective
    (f.map (k + 1)) (f.map_point (k + 1))
    (fun n ↦ homotopyGroupMap_bijective_of_isStableEquivalence hE hF f hf (k + 1) (n + 1))
  have hs : (F.structureMap k).comp (f.map k) =
      (basedLoopMap (f.map (k + 1)) (f.map_point (k + 1))).comp (E.structureMap k) := by
    apply ContinuousMap.ext
    intro x
    exact (f.comm k x).symm
  apply IsWeakHomotopyEquivalence.of_comp_right (g := F.structureMap k) _ (hF k)
  rw [hs]
  exact hl.comp (hE k)

/-- Signed stable equivalence between actual Omega-prespectra is detected by complete weakness
of the unchanged level maps, with no connectedness restriction. -/
theorem isStableEquivalence_iff_levelwise_of_isOmega :
    IsStableEquivalence f ↔ ∀ k, IsWeakHomotopyEquivalence (f.map k) :=
  ⟨fun hf k ↦ level_isWeakHomotopyEquivalence_of_isStableEquivalence hE hF f hf k,
    isStableEquivalence_of_levelwise f⟩

end Quillen.LoopPrespectrum
