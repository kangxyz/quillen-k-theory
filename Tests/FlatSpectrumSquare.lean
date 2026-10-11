/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.FlatSquare
public import Quillen.Topology.Prespectrum.StableHomotopy

/-! Consumers retaining all four original geometric arrows
and independent homotopy/structure time. -/
@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS
open scoped Topology unitInterval

universe u

namespace Quillen.Tests.FlatSpectrumSquare

variable {X Y Z W : Scheme.{u}}
  (p : X ⟶ Y) (v : Y ⟶ Z) (u : X ⟶ W) (q : W ⟶ Z)
  [Flat p] [Flat v] [Flat u] [Flat q] (h : p ≫ v = u ≫ q)

include h in
lemma original_composites_stable_eq (d : ℤ) :
    (stableHomotopyFunctor d).map
        (perfectFlatPrespectrumMap v ≫ perfectFlatPrespectrumMap p) =
      (stableHomotopyFunctor d).map
        (perfectFlatPrespectrumMap q ≫ perfectFlatPrespectrumMap u) :=
  (perfectFlatPrespectrumSquareHomotopy p v u q h).stableHomotopyMap_eq d

lemma original_structure_coordinate (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (perfectWaldhausen Z)).space n) :
    (perfectFlatPrespectrumSquareHomotopy p v u q h).level (n + 1)
        (s, (originalPrespectrum (perfectWaldhausen Z)).structureMap n x t) =
      (originalPrespectrum (perfectWaldhausen X)).structureMap n
        ((perfectFlatPrespectrumSquareHomotopy p v u q h).level n (s, x)) t :=
  (perfectFlatPrespectrumSquareHomotopy p v u q h).comm n s x t

end Quillen.Tests.FlatSpectrumSquare
