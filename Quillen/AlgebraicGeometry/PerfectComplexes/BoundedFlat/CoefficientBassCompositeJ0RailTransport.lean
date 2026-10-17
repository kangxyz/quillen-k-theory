/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeJ0UnitPasting
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeJ0RectangleRails
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassNegativeSeedReferenceRails

/-! Whole ordinary, shifted and unit simplices retain their complete composite reference data. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u v w
namespace Quillen.PerfectComplexes.CoefficientBassCompositeJ0RailTransport
open CoefficientBassNegativeSeedReferenceRails

private theorem dependent_congr {X : Sort v} {Y : X → Sort w}
    {a b : X} (f : (x : X) → Y x) (h : a = b) : HEq (f a) (f b) := by
  subst b
  rfl

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b b' c : Under R}
  (p : a ⟶ b) (q : b ⟶ c) (p' : a ⟶ b') (q' : b' ⟶ c)

/-- The ordinary simplex preserves all original full nodes under equal-composite transport. -/
theorem ordinary_heq (h : p ≫ q = p' ≫ q') (t : StdSimplex ℝ (Fin 31)) :
    HEq (CoefficientBassCompositeJ0Rectangles.ordinaryMap P p q t)
      (CoefficientBassCompositeJ0Rectangles.ordinaryMap P p' q' t) := by
  exact dependent_congr (a := seedGeometry P p q) (b := seedGeometry P p' q')
    (fun D : SeedGeometry P (a := a) (c := c) ↦ SeedGeometry.h0Point P D false t)
    (seed_geometry_eq P p q p' q' h)

/-- The shifted simplex preserves the actual common-unit anchor, not just native values. -/
theorem shifted_heq (h : p ≫ q = p' ≫ q') (t : StdSimplex ℝ (Fin 31)) :
    HEq (CoefficientBassCompositeJ0Rectangles.shiftedMap P p q t)
      (CoefficientBassCompositeJ0Rectangles.shiftedMap P p' q' t) := by
  exact dependent_congr (a := seedGeometry P p q) (b := seedGeometry P p' q')
    (fun D : SeedGeometry P (a := a) (c := c) ↦ SeedGeometry.h0Point P D true t)
    (seed_geometry_eq P p q p' q' h)

/-- The complete ten-node unit simplex retains its literal parameter and reference anchor. -/
theorem unit_heq (h : p ≫ q = p' ≫ q') (t : StdSimplex ℝ (Fin 10)) :
    HEq (CoefficientBassCompositeJ0RectangleRails.unitMap P p q t)
      (CoefficientBassCompositeJ0RectangleRails.unitMap P p' q' t) := by
  exact dependent_congr (a := seedGeometry P p q) (b := seedGeometry P p' q')
    (fun D : SeedGeometry P (a := a) (c := c) ↦ SeedGeometry.unitPoint P D t)
    (seed_geometry_eq P p q p' q' h)

/-- The entire original minus rectangle is transported at its original two coordinates. -/
theorem rectangleMinus_heq (h : p ≫ q = p' ≫ q') (r s : I) :
    HEq (CoefficientBassCompositeJ0Rectangles.rectangleMinus P p q (r, s))
      (CoefficientBassCompositeJ0Rectangles.rectangleMinus P p' q' (r, s)) := by
  rw [CoefficientBassCompositeJ0Rectangles.rectangleMinus_apply,
    CoefficientBassCompositeJ0Rectangles.rectangleMinus_apply]
  exact ordinary_heq P p q p' q' h _

/-- The entire original shifted rectangle retains its full common-unit reference. -/
theorem rectanglePlus_heq (h : p ≫ q = p' ≫ q') (r s : I) :
    HEq (CoefficientBassCompositeJ0Rectangles.rectanglePlus P p q (r, s))
      (CoefficientBassCompositeJ0Rectangles.rectanglePlus P p' q' (r, s)) := by
  rw [CoefficientBassCompositeJ0Rectangles.rectanglePlus_apply,
    CoefficientBassCompositeJ0Rectangles.rectanglePlus_apply]
  exact shifted_heq P p q p' q' h _

/-- The exact mapped and endpoint-cast five-piece unit comparison keeps every original clock. -/
theorem unitComparison_heq (h : p ≫ q = p' ≫ q') (r s : I) :
    HEq (CoefficientBassCompositeJ0UnitPasting.unitComparison P p q (r, s))
      (CoefficientBassCompositeJ0UnitPasting.unitComparison P p' q' (r, s)) := by
  rw [CoefficientBassCompositeJ0UnitPasting.unitComparison_apply,
    CoefficientBassCompositeJ0UnitPasting.unitComparison_apply]
  exact unit_heq P p q p' q' h _

end Quillen.PerfectComplexes.CoefficientBassCompositeJ0RailTransport
