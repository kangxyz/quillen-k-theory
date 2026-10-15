/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.SimplexPathEmbedding
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.DoubleSquareMergedLifts

/-! Exact scalar route paths and native triple comparisons in the merged common diagram. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Convexity
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.DoubleSquareScalarPaths

/-- The binary scalar route `0 → 1 → 2` for the source total normalization. -/
abbrev sourceTotal := binaryPath (k := 17) 0 1 2
/-- The binary scalar route `2 → 3 → 11` for the source chart normalization. -/
abbrev sourceChart := binaryPath (k := 17) 2 3 11
/-- The binary scalar route `0 → 8 → 9` to the first intermediate vertex. -/
abbrev firstIntermediate := binaryPath (k := 17) 0 8 9
/-- The binary scalar route `9 → 10 → 11` for the first restriction. -/
abbrev firstRestriction := binaryPath (k := 17) 9 10 11
/-- The binary scalar route `0 → 4 → 5` for the middle total normalization. -/
abbrev middleTotal := binaryPath (k := 17) 0 4 5
/-- The binary scalar route `5 → 6 → 13` for the middle chart normalization. -/
abbrev middleChart := binaryPath (k := 17) 5 6 13
/-- The binary scalar route `9 → 12 → 13` for the second restriction. -/
abbrev secondRestriction := binaryPath (k := 17) 9 12 13
/-- The binary scalar route `0 → 14 → 15` for the target total normalization. -/
abbrev targetTotal := binaryPath (k := 17) 0 14 15
/-- The binary scalar route `15 → 16 → 17` for the target chart normalization. -/
abbrev targetChart := binaryPath (k := 17) 15 16 17
/-- The binary scalar route `5 → 7 → 17` for the last restriction. -/
abbrev lastRestriction := binaryPath (k := 17) 5 7 17

/-- The split-triple homotopy comparing the source total/chart route with the first
intermediate/restriction route. -/
def firstComparison : (sourceTotal.trans sourceChart).Homotopy
    (firstIntermediate.trans firstRestriction) :=
  Path.Homotopy.mapOfPaths (embed DoubleSquareMergedSimplex.firstFace)
    SplitTripleSimplex.comparisonParameter _ _
    (map_splitLeft DoubleSquareMergedSimplex.firstFace)
    (map_splitRight DoubleSquareMergedSimplex.firstFace)

/-- The split-triple homotopy comparing the middle total/chart route with the
first-intermediate/second-restriction route. -/
def middleComparison : (middleTotal.trans middleChart).Homotopy
    (firstIntermediate.trans secondRestriction) :=
  Path.Homotopy.mapOfPaths (embed DoubleSquareMergedSimplex.middleFace)
    SplitTripleSimplex.comparisonParameter _ _
    (map_splitLeft DoubleSquareMergedSimplex.middleFace)
    (map_splitRight DoubleSquareMergedSimplex.middleFace)

/-- The split-triple homotopy comparing the middle-total/last-restriction route with the target
total/chart route. -/
def lastComparison : (middleTotal.trans lastRestriction).Homotopy
    (targetTotal.trans targetChart) :=
  Path.Homotopy.mapOfPaths (embed DoubleSquareMergedSimplex.lastFace)
    SplitTripleSimplex.comparisonParameter _ _
    (map_splitLeft DoubleSquareMergedSimplex.lastFace)
    (map_splitRight DoubleSquareMergedSimplex.lastFace)

variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)

theorem first_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen A)).space n) :
    prespectrumSimplexFamily (DoubleSquareMergedSimplex.simplex p q p' q' a b c hp hq) n
      (firstComparison (r, s), x) =
      (DoubleSquareTrack.firstTriple (p := p) (q := q) (c := c)).level n (r, (s, x)) :=
  DoubleSquareMergedSimplex.first_native p q p' q' a b c hp hq n r s x

theorem middle_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen A)).space n) :
    prespectrumSimplexFamily (DoubleSquareMergedSimplex.simplex p q p' q' a b c hp hq) n
      (middleComparison (r, s), x) =
      (DoubleSquareTrack.middleTriple p q q' b c hq).level n (r, (s, x)) :=
  DoubleSquareMergedSimplex.middle_native p q p' q' a b c hp hq n r s x

theorem last_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen A)).space n) :
    prespectrumSimplexFamily (DoubleSquareMergedSimplex.simplex p q p' q' a b c hp hq) n
      (lastComparison (r, s), x) =
      (DoubleSquareTrack.lastTriple p q p' q' a b c hp hq).level n (r, (s, x)) :=
  DoubleSquareMergedSimplex.last_native p q p' q' a b c hp hq n r s x
end Quillen.PerfectComplexes.DoubleSquareScalarPaths
