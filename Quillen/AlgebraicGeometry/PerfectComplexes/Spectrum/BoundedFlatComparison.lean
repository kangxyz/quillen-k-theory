/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.StableDetection
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.KComparison

/-!
# Original bounded-flat inclusion maps on positive spectrum levels

The actual bounded-flat-to-perfect inclusion on a quasi-compact scheme is a stable equivalence
and a complete weak equivalence at every original positive spectrum level. These statements keep
the literal normalized exact-functor map, without a levelwise continuous inverse or a cofiber
comparison. The stable-equivalence assertion exposes the existing K-comparison criterion.
-/
@[expose] public section
noncomputable section

open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes

/-- The literal original bounded-flat inclusion induces isomorphisms on all stable groups. -/
theorem boundedFlatPerfectInclusion_isStableEquivalence (X : Scheme.{u}) [CompactSpace X] :
    IsStableEquivalence (exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen X)
      (perfectWaldhausen X) (boundedFlatPerfectInclusion_exact X)) :=
  (exactOriginalPrespectrumMap_isStableEquivalence_iff _ _ _).mpr
    (boundedFlatPerfectToPerfectKMap_bijective X)

/-- Each original positive inclusion level is weak, including its component-surjectivity clause. -/
theorem boundedFlatPerfectInclusion_positiveLevel_isWeakHomotopyEquivalence
    (X : Scheme.{u}) [CompactSpace X] (n : ℕ) :
    IsWeakHomotopyEquivalence ((exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen X)
      (perfectWaldhausen X) (boundedFlatPerfectInclusion_exact X)).map (n + 1)) :=
  exactOriginalPrespectrumMap_positiveLevel_isWeakHomotopyEquivalence _ _ _
    (boundedFlatPerfectToPerfectKMap_bijective X) n

end Quillen.PerfectComplexes
