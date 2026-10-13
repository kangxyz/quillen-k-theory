/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassSeed
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BoundedFlatBassStep
public import Quillen.Topology.Prespectrum.StrictSquareTopology
public import Quillen.Waldhausen.SConstruction.Iterated.PointHEP

/-!
# Literal point topology for the original one-step Bass evaluation comparison

The strict section span and the original raw geometric span have genuine point HEP at every
level, including zero. The actual two cones and raw parameter-looped step inherit it. These
are the exact objects of original evaluation; no strict geometric coefficient diagram or
replacement span is used, and T1 is used only where actual loop-point closure requires it.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open Quillen.Scheme.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes

/-- The actual strict section span has HEP at every original chosen point. -/
theorem boundedFlatAffineSectionBassSpan_point_homotopyExtensionProperty
    (R : CommRingCat.{u}) (n : ℕ) :
    Quillen.homotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{u + 2}
      ((StrictSquare.span (boundedFlatAffineSectionBassSquare R)).point n))) :=
  StrictSquare.span_point_homotopyExtensionProperty _ n
    (prespectrum_point_homotopyExtensionProperty (boundedFlatAffineSectionModel R) n)
    (prespectrum_point_homotopyExtensionProperty
      (boundedFlatAffineSectionModel (.of (Polynomial R))) n)
    (prespectrum_point_homotopyExtensionProperty
      (boundedFlatAffineSectionModel (.of (Polynomial R))) n)

/-- The unchanged raw bounded-flat geometric span has genuine HEP, also at level zero. -/
theorem boundedFlatBassSpan_point_homotopyExtensionProperty (R : CommRingCat.{u}) (n : ℕ) :
    Quillen.homotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{u + 2}
      ((HomotopyPushout.prespectrum
        (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection R))).point n))) :=
  HomotopyPushout.point_homotopyExtensionProperty _ _ n
    (originalPrespectrum_point_homotopyExtensionProperty
      (boundedFlatPerfectWaldhausen (Spec R)) n)
    (originalPrespectrum_point_homotopyExtensionProperty
      (boundedFlatPerfectWaldhausen (Spec (.of (Polynomial R)))) n)
    (originalPrespectrum_point_homotopyExtensionProperty
      (boundedFlatPerfectWaldhausen (Spec (.of (Polynomial R)))) n)

/-- The actual strict section cone retains its literal well-based point in every degree. -/
theorem boundedFlatAffineSectionBassCone_point_homotopyExtensionProperty
    (R : CommRingCat.{u}) (n : ℕ) :
    Quillen.homotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{u + 2}
      ((boundedFlatAffineSectionBassCone R).point n))) :=
  ReducedMappingCone.point_homotopyExtensionProperty _ _ _
    ((StrictSquare.comparison (boundedFlatAffineSectionBassSquare R)).map_point n)
    (boundedFlatAffineSectionBassSpan_point_homotopyExtensionProperty R n)
    (prespectrum_point_homotopyExtensionProperty
      (boundedFlatAffineSectionModel (.of (LaurentPolynomial R))) n)

/-- The original raw geometric Bass cone retains HEP at every actual chosen point. -/
theorem boundedFlatBassCone_point_homotopyExtensionProperty (R : CommRingCat.{u}) (n : ℕ) :
    Quillen.homotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{u + 2}
      ((mappingCone (boundedFlatBassSquareComparison R)).point n))) :=
  ReducedMappingCone.point_homotopyExtensionProperty _ _ _
    ((boundedFlatBassSquareComparison R).map_point n)
    (boundedFlatBassSpan_point_homotopyExtensionProperty R n)
    (originalPrespectrum_point_homotopyExtensionProperty
      (boundedFlatPerfectWaldhausen (Spec (.of (LaurentPolynomial R)))) n)

/-- The unchanged raw geometric one-step parameter loop is well-based at every level. -/
theorem boundedFlatAffineBassStep_point_homotopyExtensionProperty
    (R : CommRingCat.{u}) (n : ℕ) :
    Quillen.homotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{u + 2}
      ((boundedFlatAffineBassStep R).point n))) :=
  parameterLooping_point_homotopyExtensionProperty (mappingCone (boundedFlatBassSquareComparison R))
    n isClosed_singleton (boundedFlatBassCone_point_homotopyExtensionProperty R n)

end Quillen.PerfectComplexes
