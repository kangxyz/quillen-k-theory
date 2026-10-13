/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.StableOmegaDetection
public import Quillen.Waldhausen.SConstruction.Iterated.StableFunctoriality

/-!
# Positive-level weakness of original exact-functor spectrum maps

Bijectivity of the original connective K-maps implies complete weak equivalence at every positive
level of the unchanged normalized iterated-S spectrum map. The proof uses the actual Omega
structure and proved connectedness, including component coverage; it chooses no homotopy inverse.
-/
@[expose] public section
noncomputable section

open CategoryTheory Quillen.LoopPrespectrum
universe u v
namespace Quillen.Waldhausen.IteratedS

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (W : Structure C) (V : Structure D) {F : C ⥤ D}
  (hF : IsExact W.cof W.weq V.cof V.weq F)

/-- An exact functor inducing the original K-isomorphisms is a complete weak equivalence on
every positive space of its actual normalized prespectrum map. -/
theorem exactOriginalPrespectrumMap_positiveLevel_isWeakHomotopyEquivalence
    (hK : ∀ k : ℕ, Function.Bijective (KMap hF k)) (n : ℕ) :
    IsWeakHomotopyEquivalence ((exactOriginalPrespectrumMap W V hF).map (n + 1)) :=
  positiveLevel_isWeakHomotopyEquivalence_of_isStableEquivalence
    (originalPrespectrum_isOmega W) (originalPrespectrum_isOmega V)
    (exactOriginalPrespectrumMap W V hF)
    ((exactOriginalPrespectrumMap_isStableEquivalence_iff W V hF).mpr hK)
    (fun k ↦ stageSpace_pathConnected k (modelOf W))
    (fun k ↦ stageSpace_pathConnected k (modelOf V)) n

end Quillen.Waldhausen.IteratedS
