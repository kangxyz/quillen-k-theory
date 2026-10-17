/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedCarrierAugmentation

/-! The actual augmented carrier is contractible and preserves all original cells and tips. -/
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

/-- The original minus tip retained in the full augmented carrier. -/
abbrev tipMinus := CutOpenAugmentation.tipMinus
  (polynomialReference P p q) (chartMap P (c := c)) (laurentReference P p q)
  (ordinaryAnchor P p q) (LaurentUnitReferenceSpecialization.shiftedAnchor P p q)
  (base P p q) (laurentMap P p q)

/-- The separate original plus tip retained in the full augmented carrier. -/
abbrev tipPlus := CutOpenAugmentation.tipPlus
  (polynomialReference P p q) (chartMap P (c := c)) (laurentReference P p q)
  (ordinaryAnchor P p q) (LaurentUnitReferenceSpecialization.shiftedAnchor P p q)
  (base P p q) (laurentMap P p q)

/-- The original Laurent-reference inclusion through the base of the augmented carrier. -/
abbrev laurentInclusion := CutOpenAugmentation.laurentInclusion
  (polynomialReference P p q) (chartMap P (c := c)) (laurentReference P p q)
  (ordinaryAnchor P p q) (LaurentUnitReferenceSpecialization.shiftedAnchor P p q)
  (base P p q) (laurentMap P p q)

/-- The complete original minus-sheet cylinder in the augmented carrier, with unchanged height. -/
abbrev cylinderMinus := CutOpenAugmentation.cylinderMinus
  (polynomialReference P p q) (chartMap P (c := c)) (laurentReference P p q)
  (ordinaryAnchor P p q) (LaurentUnitReferenceSpecialization.shiftedAnchor P p q)
  (base P p q) (laurentMap P p q)

/-- The complete original plus-sheet cylinder in the augmented carrier, with unchanged height. -/
abbrev cylinderPlus := CutOpenAugmentation.cylinderPlus
  (polynomialReference P p q) (chartMap P (c := c)) (laurentReference P p q)
  (ordinaryAnchor P p q) (LaurentUnitReferenceSpecialization.shiftedAnchor P p q)
  (base P p q) (laurentMap P p q)

theorem tips_ne : tipMinus P p q ≠ tipPlus P p q :=
  CutOpenAugmentation.tips_ne
  (polynomialReference P p q) (chartMap P (c := c)) (laurentReference P p q)
  (ordinaryAnchor P p q) (LaurentUnitReferenceSpecialization.shiftedAnchor P p q)
  (base P p q) (laurentMap P p q)

@[simp] theorem originalMap_tipMinus :
    originalMap P p q (CutOpenCarrier.tipMinus
      (polynomialReference P p q) (chartMap P (c := c)) (laurentReference P p q)
  (ordinaryAnchor P p q) (LaurentUnitReferenceSpecialization.shiftedAnchor P p q))
      = tipMinus P p q :=
  CutOpenAugmentation.continuousMap_tipMinus
  (polynomialReference P p q) (chartMap P (c := c)) (laurentReference P p q)
  (ordinaryAnchor P p q) (LaurentUnitReferenceSpecialization.shiftedAnchor P p q)
  (base P p q) (laurentMap P p q)

@[simp] theorem originalMap_tipPlus :
    originalMap P p q (CutOpenCarrier.tipPlus
      (polynomialReference P p q) (chartMap P (c := c)) (laurentReference P p q)
  (ordinaryAnchor P p q) (LaurentUnitReferenceSpecialization.shiftedAnchor P p q))
      = tipPlus P p q :=
  CutOpenAugmentation.continuousMap_tipPlus
  (polynomialReference P p q) (chartMap P (c := c)) (laurentReference P p q)
  (ordinaryAnchor P p q) (LaurentUnitReferenceSpecialization.shiftedAnchor P p q)
  (base P p q) (laurentMap P p q)

@[simp] theorem originalMap_laurent
    (x : |CutOpenCarrier.parameterSSet (laurentReference P p q)|) :
    originalMap P p q (CutOpenCarrier.laurentInclusion
      (polynomialReference P p q) (chartMap P (c := c)) (laurentReference P p q)
  (ordinaryAnchor P p q) (LaurentUnitReferenceSpecialization.shiftedAnchor P p q) x)
      = laurentInclusion P p q x :=
  CutOpenAugmentation.continuousMap_laurent
  (polynomialReference P p q) (chartMap P (c := c)) (laurentReference P p q)
  (ordinaryAnchor P p q) (LaurentUnitReferenceSpecialization.shiftedAnchor P p q)
  (base P p q) (laurentMap P p q) x

@[simp] theorem originalMap_cylinderMinus
    (x : |CutOpenCarrier.parameterSSet (polynomialReference P p q)|) (t : I) :
    originalMap P p q (CutOpenCarrier.cylinderMinus
      (polynomialReference P p q) (chartMap P (c := c)) (laurentReference P p q)
  (ordinaryAnchor P p q) (LaurentUnitReferenceSpecialization.shiftedAnchor P p q) (x, t))
      = cylinderMinus P p q (x, t) :=
  CutOpenAugmentation.continuousMap_cylinderMinus
  (polynomialReference P p q) (chartMap P (c := c)) (laurentReference P p q)
  (ordinaryAnchor P p q) (LaurentUnitReferenceSpecialization.shiftedAnchor P p q)
  (base P p q) (laurentMap P p q) x t

@[simp] theorem originalMap_cylinderPlus
    (x : |CutOpenCarrier.parameterSSet (polynomialReference P p q)|) (t : I) :
    originalMap P p q (CutOpenCarrier.cylinderPlus
      (polynomialReference P p q) (chartMap P (c := c)) (laurentReference P p q)
  (ordinaryAnchor P p q) (LaurentUnitReferenceSpecialization.shiftedAnchor P p q) (x, t))
      = cylinderPlus P p q (x, t) :=
  CutOpenAugmentation.continuousMap_cylinderPlus
  (polynomialReference P p q) (chartMap P (c := c)) (laurentReference P p q)
  (ordinaryAnchor P p q) (LaurentUnitReferenceSpecialization.shiftedAnchor P p q)
  (base P p q) (laurentMap P p q) x t

theorem contractibleSpace : ContractibleSpace (space P p q) := by
  let : ContractibleSpace |base P p q| := FourEdgeTree.cone_contractibleSpace
    (inputReference P p q) (BassH0Merge.normalizedMap (polynomialProjection P c))
    (BassProjectionPath.WholeReference.reference P c (inputReference P p q))
    (BassProjectionPath.WholeReference.FourEdge.beta P c (inputReference P p q))
  exact CutOpenAugmentation.contractibleSpace
    (polynomialReference P p q) (chartMap P (c := c)) (laurentReference P p q)
    (ordinaryAnchor P p q) (LaurentUnitReferenceSpecialization.shiftedAnchor P p q)
    (base P p q) (laurentMap P p q)

end Quillen.PerfectComplexes.CoefficientBassSeedCarrierAugmentation
