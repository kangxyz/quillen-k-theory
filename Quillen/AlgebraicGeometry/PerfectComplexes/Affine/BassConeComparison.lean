/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.PushoutComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BassStep
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BoundedFlatBassSquare

/-!
# Actual affine Bass cone comparison and well-basedness

The original polynomial-chart reduced pushouts and their actual square cones have HEP at their
chosen positive-level points. A supplied whole compatibility track for the original bounded-flat
and perfect Bass square comparisons then induces a complete positive-level weak equivalence on
the existing cones. All weak-equivalence and point-HEP inputs are proved here; the geometric whole
compatibility track remains an explicit hypothesis, separate from parameter looping and iteration.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes

/-- The actual bounded-flat affine Bass square cone has a well-based positive-level point. -/
theorem boundedFlatBassCone_positivePoint_homotopyExtensionProperty (R : CommRingCat.{u}) (n : ℕ) :
    Quillen.homotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{u + 2}
      ((mappingCone (boundedFlatBassSquareComparison R)).point (n + 1)))) :=
  mappingCone_positivePoint_homotopyExtensionProperty _
    (boundedFlatFlatPullbackPushout_positivePoint_homotopyExtensionProperty
      (polynomialProjection R) (polynomialProjection R))
    (originalPrespectrum_positivePoint_homotopyExtensionProperty
      (boundedFlatPerfectWaldhausen (Spec (.of (LaurentPolynomial R))))) n

/-- The actual perfect affine Bass square cone has a well-based positive-level point. -/
theorem bassCone_positivePoint_homotopyExtensionProperty (R : CommRingCat.{u}) (n : ℕ) :
    Quillen.homotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{u + 2}
      ((mappingCone (bassSquareComparison R)).point (n + 1)))) :=
  mappingCone_positivePoint_homotopyExtensionProperty _
    (perfectFlatPullbackPushout_positivePoint_homotopyExtensionProperty
      (polynomialProjection R) (polynomialProjection R))
    (originalPrespectrum_positivePoint_homotopyExtensionProperty
      (perfectWaldhausen (Spec (.of (LaurentPolynomial R))))) n

variable (R : CommRingCat.{u})
  (H : Homotopy
    (boundedFlatBassSquareComparison R ≫
      exactOriginalPrespectrumMap
        (boundedFlatPerfectWaldhausen (Spec (.of (LaurentPolynomial R))))
        (perfectWaldhausen (Spec (.of (LaurentPolynomial R))))
        (boundedFlatPerfectInclusion_exact (Spec (.of (LaurentPolynomial R)))))
    (boundedFlatPerfectFlatPullbackPushoutMap (polynomialProjection R) (polynomialProjection R) ≫
      bassSquareComparison R))

/-- The literal original cone-square map for a supplied whole affine Bass compatibility track. -/
def boundedFlatPerfectBassConeMap :
    mappingCone (boundedFlatBassSquareComparison R) ⟶ mappingCone (bassSquareComparison R) :=
  mappingConeSquareMap _ _
    (boundedFlatPerfectFlatPullbackPushoutMap (polynomialProjection R) (polynomialProjection R))
    (exactOriginalPrespectrumMap
      (boundedFlatPerfectWaldhausen (Spec (.of (LaurentPolynomial R))))
      (perfectWaldhausen (Spec (.of (LaurentPolynomial R))))
      (boundedFlatPerfectInclusion_exact (Spec (.of (LaurentPolynomial R))))) H

/-- Every original positive cone level is completely weakly equivalent; only the displayed whole
geometric compatibility track remains supplied. -/
theorem boundedFlatPerfectBassConeMap_positiveLevel_isWeakHomotopyEquivalence (n : ℕ) :
    IsWeakHomotopyEquivalence ((boundedFlatPerfectBassConeMap R H).map (n + 1)) :=
  mappingConeSquareMap_positiveLevel_isWeakHomotopyEquivalence _ _ _ _ H
    (boundedFlatFlatPullbackPushout_positivePoint_homotopyExtensionProperty
      (polynomialProjection R) (polynomialProjection R))
    (originalPrespectrum_positivePoint_homotopyExtensionProperty
      (boundedFlatPerfectWaldhausen (Spec (.of (LaurentPolynomial R)))))
    (perfectFlatPullbackPushout_positivePoint_homotopyExtensionProperty
      (polynomialProjection R) (polynomialProjection R))
    (originalPrespectrum_positivePoint_homotopyExtensionProperty
      (perfectWaldhausen (Spec (.of (LaurentPolynomial R)))))
    (boundedFlatPerfectFlatPullbackPushoutMap_positiveLevel_isWeakHomotopyEquivalence
      (polynomialProjection R) (polynomialProjection R))
    (boundedFlatPerfectInclusion_positiveLevel_isWeakHomotopyEquivalence
      (Spec (.of (LaurentPolynomial R)))) n

/-- The unchanged signed stable groups of the actual Bass cones agree along this original map. -/
theorem boundedFlatPerfectBassConeMap_isStableEquivalence :
    IsStableEquivalence (boundedFlatPerfectBassConeMap R H) :=
  isStableEquivalence_of_positiveLevel _
    (boundedFlatPerfectBassConeMap_positiveLevel_isWeakHomotopyEquivalence R H)

end Quillen.PerfectComplexes
