/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BassInclusionComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BassStepComparison

/-!
# Unconditional original geometric Bass-step comparison

The actual geometric inclusion homotopy supplies the missing whole-track input to the original
cone comparison. The resulting cone and parameter-looping maps are complete weak equivalences in
every positive level and stable equivalences in every integer degree. These are the original
bounded-flat and perfect one-step Bass constructions, with no supplied compatibility premise.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
variable (R : CommRingCat.{u})

/-- The original cone-square map with its proved geometric inclusion track. -/
def boundedFlatPerfectGeometricBassConeMap :
    mappingCone (boundedFlatBassSquareComparison R) ⟶ mappingCone (bassSquareComparison R) :=
  boundedFlatPerfectBassConeMap R (boundedFlatPerfectBassComparisonHomotopy R)

/-- The unchanged geometric cone map is a complete weak equivalence in every positive level. -/
theorem boundedFlatPerfectGeometricBassConeMap_positiveLevel_isWeakHomotopyEquivalence (n : ℕ) :
    IsWeakHomotopyEquivalence ((boundedFlatPerfectGeometricBassConeMap R).map (n + 1)) :=
  boundedFlatPerfectBassConeMap_positiveLevel_isWeakHomotopyEquivalence R
    (boundedFlatPerfectBassComparisonHomotopy R) n

/-- The original geometric Bass cones agree on every signed stable group. -/
theorem boundedFlatPerfectGeometricBassConeMap_isStableEquivalence :
    IsStableEquivalence (boundedFlatPerfectGeometricBassConeMap R) :=
  boundedFlatPerfectBassConeMap_isStableEquivalence R (boundedFlatPerfectBassComparisonHomotopy R)

/-- The actual looped Bass-step comparison uses the proved geometric cone-square map. -/
def boundedFlatPerfectGeometricBassStepMap : boundedFlatAffineBassStep R ⟶ affineBassStep R :=
  boundedFlatPerfectBassStepMap R (boundedFlatPerfectBassComparisonHomotopy R)

/-- All components and homotopy groups of original positive Bass-step levels are preserved. -/
theorem boundedFlatPerfectGeometricBassStepMap_positiveLevel_isWeakHomotopyEquivalence (n : ℕ) :
    IsWeakHomotopyEquivalence ((boundedFlatPerfectGeometricBassStepMap R).map (n + 1)) :=
  boundedFlatPerfectBassStepMap_positiveLevel_isWeakHomotopyEquivalence R
    (boundedFlatPerfectBassComparisonHomotopy R) n

/-- The original one-step bounded-flat/perfect comparison is a stable equivalence. -/
theorem boundedFlatPerfectGeometricBassStepMap_isStableEquivalence :
    IsStableEquivalence (boundedFlatPerfectGeometricBassStepMap R) :=
  boundedFlatPerfectBassStepMap_isStableEquivalence R (boundedFlatPerfectBassComparisonHomotopy R)

end Quillen.PerfectComplexes
