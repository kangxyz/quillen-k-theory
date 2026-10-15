/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BassConeComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BoundedFlatBassStep
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BassStepSeparation
public import Quillen.Topology.Prespectrum.ParameterLoopingPointHEP
public import Quillen.Topology.Prespectrum.ParameterLoopingWeakEquivalence

/-!
# Original affine Bass-step preservation under parameter looping

The original bounded-flat and perfect affine Bass steps have HEP at their actual
positive-level constant-loop points. The proof uses the established cone-point
HEP and actual T1 separation, followed by the literal compact-open loop theorem.

The unchanged parameter-looping of the original whole-square cone comparison
is a complete weak equivalence at every positive level, hence a stable
equivalence. Its geometric compatibility homotopy remains an explicit input;
no iterated Bass tower or fundamental theorem is assumed.
-/
@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes

/-- The original bounded-flat affine Bass-step point has HEP in every positive level. -/
theorem boundedFlatAffineBassStep_positivePoint_homotopyExtensionProperty
    (R : CommRingCat.{u}) (n : ℕ) :
    Quillen.homotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{u + 2}
      ((boundedFlatAffineBassStep R).point (n + 1)))) :=
  parameterLooping_point_homotopyExtensionProperty _ (n + 1) isClosed_singleton
    (boundedFlatBassCone_positivePoint_homotopyExtensionProperty R n)

/-- The original perfect affine Bass-step point has HEP in every positive level. -/
theorem affineBassStep_positivePoint_homotopyExtensionProperty
    (R : CommRingCat.{u}) (n : ℕ) :
    Quillen.homotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{u + 2}
      ((affineBassStep R).point (n + 1)))) :=
  parameterLooping_point_homotopyExtensionProperty _ (n + 1) isClosed_singleton
    (bassCone_positivePoint_homotopyExtensionProperty R n)

variable (R : CommRingCat.{u})
  (H : Homotopy
    (boundedFlatBassSquareComparison R ≫
      exactOriginalPrespectrumMap
        (boundedFlatPerfectWaldhausen (Spec (.of (LaurentPolynomial R))))
        (perfectWaldhausen (Spec (.of (LaurentPolynomial R))))
        (boundedFlatPerfectInclusion_exact (Spec (.of (LaurentPolynomial R)))))
    (boundedFlatPerfectFlatPullbackPushoutMap (polynomialProjection R) (polynomialProjection R) ≫
      bassSquareComparison R))

/-- The actual parameter-looping of the original cone map with its supplied geometric track. -/
def boundedFlatPerfectBassStepMap : boundedFlatAffineBassStep R ⟶ affineBassStep R :=
  parameterLoopingMap (boundedFlatPerfectBassConeMap R H)

/-- Original positive Bass-step levels are completely weakly equivalent along the actual map. -/
theorem boundedFlatPerfectBassStepMap_positiveLevel_isWeakHomotopyEquivalence (n : ℕ) :
    IsWeakHomotopyEquivalence ((boundedFlatPerfectBassStepMap R H).map (n + 1)) :=
  parameterLoopingMap_positiveLevel_isWeakHomotopyEquivalence _
    (boundedFlatPerfectBassConeMap_positiveLevel_isWeakHomotopyEquivalence R H) n

/-- The actual Bass-step comparison induces isomorphisms on the original signed stable groups. -/
theorem boundedFlatPerfectBassStepMap_isStableEquivalence :
    IsStableEquivalence (boundedFlatPerfectBassStepMap R H) :=
  parameterLoopingMap_isStableEquivalence_of_positiveLevel _
    (boundedFlatPerfectBassConeMap_positiveLevel_isWeakHomotopyEquivalence R H)

end Quillen.PerfectComplexes
