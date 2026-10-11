/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.BoundedFlatComparison
public import Quillen.Waldhausen.SConstruction.Iterated.VertexHEP
public import Quillen.Topology.Prespectrum.MappingConeWeakEquivalence

/-!
# Original cone comparison for strict bounded-flat inclusion squares

For a strictly commuting square between specified original bounded-flat and perfect spectrum
arrows on quasi-compact schemes, the literal existing cone map is a stable equivalence. The side
weak equivalences and all four chosen-point HEP hypotheses are proved for those actual models.
Homotopy-commuting Bass squares and their retained tracks require a further comparison.
-/
@[expose] public section
noncomputable section

open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes

/-- A strict square with the actual bounded-flat inclusions transports the original reduced cone,
using proved weak side maps and HEP at the unchanged S-vertices. -/
theorem boundedFlatPerfectConeMap_isStableEquivalence
    (X Y : Scheme.{u}) [CompactSpace X] [CompactSpace Y]
    (f : originalPrespectrum (boundedFlatPerfectWaldhausen X) ⟶
      originalPrespectrum (boundedFlatPerfectWaldhausen Y))
    (g : originalPrespectrum (perfectWaldhausen X) ⟶ originalPrespectrum (perfectWaldhausen Y))
    (w : exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen X) (perfectWaldhausen X)
        (boundedFlatPerfectInclusion_exact X) ≫ g =
      f ≫ exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen Y) (perfectWaldhausen Y)
        (boundedFlatPerfectInclusion_exact Y)) :
    IsStableEquivalence (mappingConeMap (Arrow.homMk (f := Arrow.mk f) (g := Arrow.mk g)
      (exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen X) (perfectWaldhausen X)
        (boundedFlatPerfectInclusion_exact X))
      (exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen Y) (perfectWaldhausen Y)
        (boundedFlatPerfectInclusion_exact Y)) w)) :=
  mappingConeMap_isStableEquivalence_of_positiveLevel _
    (originalPrespectrum_positivePoint_homotopyExtensionProperty (boundedFlatPerfectWaldhausen X))
    (originalPrespectrum_positivePoint_homotopyExtensionProperty (boundedFlatPerfectWaldhausen Y))
    (originalPrespectrum_positivePoint_homotopyExtensionProperty (perfectWaldhausen X))
    (originalPrespectrum_positivePoint_homotopyExtensionProperty (perfectWaldhausen Y))
    (boundedFlatPerfectInclusion_positiveLevel_isWeakHomotopyEquivalence X)
    (boundedFlatPerfectInclusion_positiveLevel_isWeakHomotopyEquivalence Y)

end Quillen.PerfectComplexes
