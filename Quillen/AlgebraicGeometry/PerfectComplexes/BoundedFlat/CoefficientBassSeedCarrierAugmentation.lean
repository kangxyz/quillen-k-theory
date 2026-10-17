/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCutOpenAugmentationTopology
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedCarrierLaurentReference
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeMap

/-! The actual original two sheets adjoin to the full unreduced two-chart carrier. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedCarrierAugmentation
open CommonReferenceNerve CoefficientBassPositiveC1BoundaryLift
open CoefficientBassSeedCarrierLaurentReference
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The whole original two-chart tree cone, before either additional original sheet. -/
abbrev base := FourEdgeTree.cone (inputReference P p q)
  (BassH0Merge.normalizedMap (polynomialProjection P c))
  (BassProjectionPath.WholeReference.reference P c (inputReference P p q))
  (BassProjectionPath.WholeReference.FourEdge.beta P c (inputReference P p q))

/-- The exact full Laurent reference is reanchored before entering the base carrier. -/
def laurentMap : CutOpenCarrier.parameterSSet (laurentReference P p q) ⟶ base P p q :=
  nerveMap (Codiscrete.functorOfFun (nodeMap P p q)) ≫
    FourEdgeTree.coneLaurent (inputReference P p q)
      (BassH0Merge.normalizedMap (polynomialProjection P c))
      (BassProjectionPath.WholeReference.reference P c (inputReference P p q))
      (BassProjectionPath.WholeReference.FourEdge.beta P c (inputReference P p q))

/-- Both original anchors and both separate tips are retained literally. -/
abbrev scalar := CutOpenAugmentation.simplicial
  (polynomialReference P p q) (chartMap P (c := c)) (laurentReference P p q)
  (ordinaryAnchor P p q) (LaurentUnitReferenceSpecialization.shiftedAnchor P p q)
  (base P p q) (laurentMap P p q)

/-- The realized augmented two-chart carrier containing both original polynomial sheets. -/
abbrev space : TopCat.{u + 1} := |scalar P p q|

/-- The existing filled positive carrier enters the larger scalar carrier as a whole. -/
def originalMap : C(CoefficientBassPositiveC0CarrierSeed.Carrier P p q, space P p q) :=
  CutOpenAugmentation.continuousMap
    (polynomialReference P p q) (chartMap P (c := c)) (laurentReference P p q)
    (ordinaryAnchor P p q) (LaurentUnitReferenceSpecialization.shiftedAnchor P p q)
    (base P p q) (laurentMap P p q)

end Quillen.PerfectComplexes.CoefficientBassSeedCarrierAugmentation
