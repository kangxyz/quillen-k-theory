/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.ConeHomotopyComparison
public import Quillen.Topology.Prespectrum.PushoutHomotopySquareEquivalence

/-!
# Original reduced-pushout comparison for bounded-flat inclusion

The actual bounded-flat/perfect inclusions and their original flat-pullback normalization tracks
induce a whole-track map between the existing reduced homotopy pushouts. Its positive levels are
complete weak equivalences on quasi-compact schemes, hence its original signed stable map is an
isomorphism. All chosen-point HEP hypotheses are proved for the literal iterated-S vertices.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes

/-- The actual whole-track reduced-pushout map for two original flat geometric pullbacks. -/
def boundedFlatPerfectFlatPullbackPushoutMap {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ X) [Flat f] [Flat g] :
    HomotopyPushout.prespectrum (boundedFlatPerfectPrespectrumMap f)
      (boundedFlatPerfectPrespectrumMap g) ⟶
    HomotopyPushout.prespectrum (perfectFlatPrespectrumMap f) (perfectFlatPrespectrumMap g) :=
  HomotopyPushout.mapOfHomotopies _ _ _ _
    (exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen X) (perfectWaldhausen X)
      (boundedFlatPerfectInclusion_exact X))
    (exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen Y) (perfectWaldhausen Y)
      (boundedFlatPerfectInclusion_exact Y))
    (exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen Z) (perfectWaldhausen Z)
      (boundedFlatPerfectInclusion_exact Z))
    (boundedFlatPerfectInclusionFlatPullbackHomotopy f)
    (boundedFlatPerfectInclusionFlatPullbackHomotopy g)

/-- Every actual positive-level geometric pushout comparison is a complete weak equivalence. -/
theorem boundedFlatPerfectFlatPullbackPushoutMap_positiveLevel_isWeakHomotopyEquivalence
    {X Y Z : Scheme.{u}} [CompactSpace X] [CompactSpace Y] [CompactSpace Z]
    (f : Y ⟶ X) (g : Z ⟶ X) [Flat f] [Flat g] (n : ℕ) :
    IsWeakHomotopyEquivalence ((boundedFlatPerfectFlatPullbackPushoutMap f g).map (n + 1)) :=
  HomotopyPushout.mapOfHomotopies_level_isWeakHomotopyEquivalence _ _ _ _ _ _ _ _ _ (n + 1)
    (originalPrespectrum_positivePoint_homotopyExtensionProperty (boundedFlatPerfectWaldhausen X) n)
    (originalPrespectrum_positivePoint_homotopyExtensionProperty (boundedFlatPerfectWaldhausen Y) n)
    (originalPrespectrum_positivePoint_homotopyExtensionProperty (boundedFlatPerfectWaldhausen Z) n)
    (originalPrespectrum_positivePoint_homotopyExtensionProperty (perfectWaldhausen X) n)
    (originalPrespectrum_positivePoint_homotopyExtensionProperty (perfectWaldhausen Y) n)
    (originalPrespectrum_positivePoint_homotopyExtensionProperty (perfectWaldhausen Z) n)
    (boundedFlatPerfectInclusion_positiveLevel_isWeakHomotopyEquivalence X n)
    (boundedFlatPerfectInclusion_positiveLevel_isWeakHomotopyEquivalence Y n)
    (boundedFlatPerfectInclusion_positiveLevel_isWeakHomotopyEquivalence Z n)

/-- The actual flat-pullback pushout comparison preserves the unchanged signed stable groups. -/
theorem boundedFlatPerfectFlatPullbackPushoutMap_isStableEquivalence
    {X Y Z : Scheme.{u}} [CompactSpace X] [CompactSpace Y] [CompactSpace Z]
    (f : Y ⟶ X) (g : Z ⟶ X) [Flat f] [Flat g] :
    IsStableEquivalence (boundedFlatPerfectFlatPullbackPushoutMap f g) :=
  isStableEquivalence_of_positiveLevel _
    (boundedFlatPerfectFlatPullbackPushoutMap_positiveLevel_isWeakHomotopyEquivalence f g)

/-- The original bounded-flat reduced-pushout point has HEP at every positive level. -/
theorem boundedFlatFlatPullbackPushout_positivePoint_homotopyExtensionProperty
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ X) (n : ℕ) :
    Quillen.homotopyExtensionProperty (HomotopyPushout.reducedPoint
      (boundedFlatPerfectPrespectrumMap f) (boundedFlatPerfectPrespectrumMap g) (n + 1)) :=
  HomotopyPushout.point_homotopyExtensionProperty _ _ _
    (originalPrespectrum_positivePoint_homotopyExtensionProperty (boundedFlatPerfectWaldhausen X) n)
    (originalPrespectrum_positivePoint_homotopyExtensionProperty (boundedFlatPerfectWaldhausen Y) n)
    (originalPrespectrum_positivePoint_homotopyExtensionProperty (boundedFlatPerfectWaldhausen Z) n)

/-- The original perfect reduced-pushout point has HEP at every positive level. -/
theorem perfectFlatPullbackPushout_positivePoint_homotopyExtensionProperty
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ X) [Flat f] [Flat g] (n : ℕ) :
    Quillen.homotopyExtensionProperty (HomotopyPushout.reducedPoint
      (perfectFlatPrespectrumMap f) (perfectFlatPrespectrumMap g) (n + 1)) :=
  HomotopyPushout.point_homotopyExtensionProperty _ _ _
    (originalPrespectrum_positivePoint_homotopyExtensionProperty (perfectWaldhausen X) n)
    (originalPrespectrum_positivePoint_homotopyExtensionProperty (perfectWaldhausen Y) n)
    (originalPrespectrum_positivePoint_homotopyExtensionProperty (perfectWaldhausen Z) n)

end Quillen.PerfectComplexes
