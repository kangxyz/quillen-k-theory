/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.BoundedFlatComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.BoundedFlatPullback
public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.GlobalUnit
public import Quillen.Waldhausen.SConstruction.Iterated.VertexHEP
public import Quillen.Topology.Prespectrum.ConeHomotopySquareEquivalence

/-!
# Original cone comparison for whole bounded-flat inclusion squares

A supplied whole square track between the original bounded-flat and perfect spectrum arrows gives
a stable equivalence on the existing mappingConeSquareMap, with all weak and well-based inputs
proved for the actual models. For flat geometric pullback the required track is constructed from
the two original exact-functor normalization comparisons, so its cone comparison requires no
additional supplied square. The complete Bass double-cylinder step remains a separate claim.
-/
@[expose] public section
noncomputable section

open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes

/-- The original supplied homotopy-square cone map is stable for actual bounded-flat inclusions. -/
theorem boundedFlatPerfectConeSquareMap_isStableEquivalence
    (X Y : Scheme.{u}) [CompactSpace X] [CompactSpace Y]
    (f : originalPrespectrum (boundedFlatPerfectWaldhausen X) ⟶
      originalPrespectrum (boundedFlatPerfectWaldhausen Y))
    (g : originalPrespectrum (perfectWaldhausen X) ⟶ originalPrespectrum (perfectWaldhausen Y))
    (H : Homotopy
      (f ≫ exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen Y) (perfectWaldhausen Y)
        (boundedFlatPerfectInclusion_exact Y))
      (exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen X) (perfectWaldhausen X)
        (boundedFlatPerfectInclusion_exact X) ≫ g)) :
    IsStableEquivalence (mappingConeSquareMap f g
      (exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen X) (perfectWaldhausen X)
        (boundedFlatPerfectInclusion_exact X))
      (exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen Y) (perfectWaldhausen Y)
        (boundedFlatPerfectInclusion_exact Y)) H) :=
  mappingConeSquareMap_isStableEquivalence_of_positiveLevel _ _ _ _ _
    (originalPrespectrum_positivePoint_homotopyExtensionProperty (boundedFlatPerfectWaldhausen X))
    (originalPrespectrum_positivePoint_homotopyExtensionProperty (boundedFlatPerfectWaldhausen Y))
    (originalPrespectrum_positivePoint_homotopyExtensionProperty (perfectWaldhausen X))
    (originalPrespectrum_positivePoint_homotopyExtensionProperty (perfectWaldhausen Y))
    (boundedFlatPerfectInclusion_positiveLevel_isWeakHomotopyEquivalence X)
    (boundedFlatPerfectInclusion_positiveLevel_isWeakHomotopyEquivalence Y)

/-- The actual flat-pullback inclusion square retains the two original normalization tracks. -/
def boundedFlatPerfectInclusionFlatPullbackHomotopy
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    Homotopy
      (boundedFlatPerfectPrespectrumMap f ≫
        exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen X) (perfectWaldhausen X)
          (boundedFlatPerfectInclusion_exact X))
      (exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen Y) (perfectWaldhausen Y)
        (boundedFlatPerfectInclusion_exact Y) ≫ perfectFlatPrespectrumMap f) :=
  (exactOriginalPrespectrumMapCompHomotopy _ _ _
    (boundedFlatPerfectPullback_exact f) (boundedFlatPerfectInclusion_exact X)).symm.trans
      (exactOriginalPrespectrumMapCompHomotopy _ _ _
        (boundedFlatPerfectInclusion_exact Y) (perfectFlatPullback_waldhausenExact f))

/-- The literal whole-track cone map compares the two original flat geometric pullback arrows. -/
def boundedFlatPerfectFlatPullbackConeMap {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    mappingCone (boundedFlatPerfectPrespectrumMap f) ⟶ mappingCone (perfectFlatPrespectrumMap f) :=
  mappingConeSquareMap (boundedFlatPerfectPrespectrumMap f) (perfectFlatPrespectrumMap f)
    (exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen Y) (perfectWaldhausen Y)
      (boundedFlatPerfectInclusion_exact Y))
    (exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen X) (perfectWaldhausen X)
      (boundedFlatPerfectInclusion_exact X)) (boundedFlatPerfectInclusionFlatPullbackHomotopy f)

/-- The actual flat geometric pullback cone comparison is stable on quasi-compact schemes. -/
theorem boundedFlatPerfectFlatPullbackConeMap_isStableEquivalence
    {X Y : Scheme.{u}} [CompactSpace X] [CompactSpace Y] (f : X ⟶ Y) [Flat f] :
    IsStableEquivalence (boundedFlatPerfectFlatPullbackConeMap f) :=
  boundedFlatPerfectConeSquareMap_isStableEquivalence Y X
    (boundedFlatPerfectPrespectrumMap f) (perfectFlatPrespectrumMap f)
    (boundedFlatPerfectInclusionFlatPullbackHomotopy f)

end Quillen.PerfectComplexes
