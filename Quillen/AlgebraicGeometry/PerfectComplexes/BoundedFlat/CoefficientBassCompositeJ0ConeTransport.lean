/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassNegativeCarrierReference
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeJ0ConeBoundaries
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeJ0PolynomialTransport

/-! Both original polynomial cone squares retain their complete reference and cylinder clocks. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u v w
namespace Quillen.PerfectComplexes.CoefficientBassCompositeJ0ConeTransport
open CoefficientBassNegativeSeedReferenceRails

private theorem dependent_congr {X : Sort v} {Y : X → Sort w}
    {a b : X} (f : (x : X) → Y x) (h : a = b) : HEq (f a) (f b) := by
  subst b
  rfl

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b b' c : Under R}
  (p : a ⟶ b) (q : b ⟶ c) (p' : a ⟶ b') (q' : b' ⟶ c)

/-- The entire original minus cone square transports with its full polynomial movement. -/
theorem coneSquareMinus_heq (h : p ≫ q = p' ≫ q') (r s : I) :
    HEq ((CoefficientBassCompositeJ0ConeBoundaries.coneSquareMinus P p q).parameter (r, s))
      ((CoefficientBassCompositeJ0ConeBoundaries.coneSquareMinus P p' q').parameter (r, s)) := by
  change HEq
    (SeedGeometry.minusCylinder P (seedGeometry P p q)
      (CoefficientBassCompositeJ0Polynomial.movement P p q r, s))
    (SeedGeometry.minusCylinder P (seedGeometry P p' q')
      (CoefficientBassCompositeJ0Polynomial.movement P p' q' r, s))
  rw [CoefficientBassCompositeJ0PolynomialTransport.movement_normal,
    CoefficientBassCompositeJ0PolynomialTransport.movement_normal]
  exact dependent_congr (a := seedGeometry P p q) (b := seedGeometry P p' q')
    (fun D : SeedGeometry P (a := a) (c := c) ↦ SeedGeometry.minusCylinder P D
      (CoefficientBassCompositeJ0PolynomialTransport.movement P D r, s))
    (seed_geometry_eq P p q p' q' h)

/-- The entire original plus cone square transports with its full polynomial movement. -/
theorem coneSquarePlus_heq (h : p ≫ q = p' ≫ q') (r s : I) :
    HEq ((CoefficientBassCompositeJ0ConeBoundaries.coneSquarePlus P p q).parameter (r, s))
      ((CoefficientBassCompositeJ0ConeBoundaries.coneSquarePlus P p' q').parameter (r, s)) := by
  change HEq
    (SeedGeometry.plusCylinder P (seedGeometry P p q)
      (CoefficientBassCompositeJ0Polynomial.movement P p q r, s))
    (SeedGeometry.plusCylinder P (seedGeometry P p' q')
      (CoefficientBassCompositeJ0Polynomial.movement P p' q' r, s))
  rw [CoefficientBassCompositeJ0PolynomialTransport.movement_normal,
    CoefficientBassCompositeJ0PolynomialTransport.movement_normal]
  exact dependent_congr (a := seedGeometry P p q) (b := seedGeometry P p' q')
    (fun D : SeedGeometry P (a := a) (c := c) ↦ SeedGeometry.plusCylinder P D
      (CoefficientBassCompositeJ0PolynomialTransport.movement P D r, s))
    (seed_geometry_eq P p q p' q' h)

/-- Actual carrier transport preserves the complete minus square pointwise. -/
theorem coneSquareMinus_transport (h : p ≫ q = p' ≫ q') (r s : I) :
    CoefficientBassNegativeCarrierReference.transport P p q p' q' h
      ((CoefficientBassCompositeJ0ConeBoundaries.coneSquareMinus P p q).parameter (r, s)) =
      (CoefficientBassCompositeJ0ConeBoundaries.coneSquareMinus P p' q').parameter (r, s) :=
  eq_of_heq ((CoefficientBassNegativeCarrierReference.transport_heq P p q p' q' h _).trans
    (coneSquareMinus_heq P p q p' q' h r s))

/-- The original minus collapse and terminal-pause cancellation commute with actual transport. -/
theorem coneBoundaryMinus_transport (h : p ≫ q = p' ≫ q') (r s : I) :
    CoefficientBassNegativeCarrierReference.transport P p q p' q' h
      (CoefficientBassCompositeJ0ConeBoundaries.coneBoundaryMinus P p q (r, s)) =
      CoefficientBassCompositeJ0ConeBoundaries.coneBoundaryMinus P p' q' (r, s) :=
  (CoefficientBassCompositeJ0ConeBoundaries.coneSquareMinus P p q).coneBoundary_natural
    (CoefficientBassCompositeJ0ConeBoundaries.coneSquareMinus P p' q')
    (CoefficientBassNegativeCarrierReference.transport P p q p' q' h)
    (coneSquareMinus_transport P p q p' q' h) r s

/-- Actual carrier transport preserves the complete plus square pointwise. -/
theorem coneSquarePlus_transport (h : p ≫ q = p' ≫ q') (r s : I) :
    CoefficientBassNegativeCarrierReference.transport P p q p' q' h
      ((CoefficientBassCompositeJ0ConeBoundaries.coneSquarePlus P p q).parameter (r, s)) =
      (CoefficientBassCompositeJ0ConeBoundaries.coneSquarePlus P p' q').parameter (r, s) :=
  eq_of_heq ((CoefficientBassNegativeCarrierReference.transport_heq P p q p' q' h _).trans
    (coneSquarePlus_heq P p q p' q' h r s))

/-- The original plus collapse and terminal-pause cancellation commute with actual transport. -/
theorem coneBoundaryPlus_transport (h : p ≫ q = p' ≫ q') (r s : I) :
    CoefficientBassNegativeCarrierReference.transport P p q p' q' h
      (CoefficientBassCompositeJ0ConeBoundaries.coneBoundaryPlus P p q (r, s)) =
      CoefficientBassCompositeJ0ConeBoundaries.coneBoundaryPlus P p' q' (r, s) :=
  (CoefficientBassCompositeJ0ConeBoundaries.coneSquarePlus P p q).coneBoundary_natural
    (CoefficientBassCompositeJ0ConeBoundaries.coneSquarePlus P p' q')
    (CoefficientBassNegativeCarrierReference.transport P p q p' q' h)
    (coneSquarePlus_transport P p q p' q' h) r s

end Quillen.PerfectComplexes.CoefficientBassCompositeJ0ConeTransport
