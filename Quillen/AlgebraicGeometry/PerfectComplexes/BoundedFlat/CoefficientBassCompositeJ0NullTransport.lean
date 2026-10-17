/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeJ0ConeTransport
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeJ0RailTransport
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeJ0PairedNull
public import Quillen.Topology.Path.NullWordEvaluation

/-! Actual equal-composite transport preserves both original five-stage pasted-null words. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassCompositeJ0NullTransport
open CoefficientBassCompositeJ0Rectangles CoefficientBassCompositeJ0PairedNull
open CoefficientBassCompositeJ0RailTransport CoefficientBassCompositeJ0ConeTransport
open CoefficientBassNegativeCarrierReference
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b b' c : Under R}
  (p : a ⟶ b) (q : b ⟶ c) (p' : a ⟶ b') (q' : b' ⟶ c)

/-- The complete ordinary simplex commutes with the actual carrier transport. -/
theorem ordinary_transport (h : p ≫ q = p' ≫ q') (t : StdSimplex ℝ (Fin 31)) :
    transport P p q p' q' h (ordinaryMap P p q t) = ordinaryMap P p' q' t :=
  eq_of_heq ((transport_heq P p q p' q' h _).trans
    (ordinary_heq P p q p' q' h t))

/-- The original minus pasted-null word retains every nested comparison and path clock. -/
theorem pastedNullMinus_transport (h : p ≫ q = p' ≫ q') (r s : I) :
    transport P p q p' q' h (pastedNullMinus P p q (r, s)) =
      pastedNullMinus P p' q' (r, s) := by
  refine Path.Evaluation.pastedPositiveNullWord (transport P p q p' q' h)
    (oldPositiveMinus P p q) (positiveMovementMinus P p q)
    (polynomialMovementMinus P p q) (laurentMovementMinus P p q)
    (newPositiveMinus P p q) (oldConeMinus P p q) (newConeMinus P p q)
    (oldPositiveMinus P p' q') (positiveMovementMinus P p' q')
    (polynomialMovementMinus P p' q') (laurentMovementMinus P p' q')
    (newPositiveMinus P p' q') (oldConeMinus P p' q') (newConeMinus P p' q')
    (rectangleMinus P p q) (rectangleMinus P p' q')
    (coneComparisonMinus P p q) (coneComparisonMinus P p' q')
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ r s
  · intro t
    exact ordinary_transport P p q p' q' h _
  · intro t
    exact ordinary_transport P p q p' q' h _
  · intro t
    exact ordinary_transport P p q p' q' h _
  · intro t
    exact ordinary_transport P p q p' q' h _
  · intro t
    exact ordinary_transport P p q p' q' h _
  · intro t
    exact coneSquareMinus_transport P p q p' q' h 0 t
  · intro t
    exact coneSquareMinus_transport P p q p' q' h 1 t
  · intro u v
    exact eq_of_heq ((transport_heq P p q p' q' h _).trans
      (rectangleMinus_heq P p q p' q' h u v))
  · intro u v
    rw [coneComparisonMinus_apply, coneComparisonMinus_apply]
    exact coneBoundaryMinus_transport P p q p' q' h u v

/-- The complete shifted simplex commutes with the actual carrier transport. -/
theorem shifted_transport (h : p ≫ q = p' ≫ q') (t : StdSimplex ℝ (Fin 31)) :
    transport P p q p' q' h (shiftedMap P p q t) = shiftedMap P p' q' t :=
  eq_of_heq ((transport_heq P p q p' q' h _).trans
    (shifted_heq P p q p' q' h t))

/-- The original plus pasted-null word retains every nested comparison and path clock. -/
theorem pastedNullPlus_transport (h : p ≫ q = p' ≫ q') (r s : I) :
    transport P p q p' q' h (pastedNullPlus P p q (r, s)) =
      pastedNullPlus P p' q' (r, s) := by
  refine Path.Evaluation.pastedPositiveNullWord (transport P p q p' q' h)
    (oldPositivePlus P p q) (positiveMovementPlus P p q)
    (polynomialMovementPlus P p q) (laurentMovementPlus P p q)
    (newPositivePlus P p q) (oldConePlus P p q) (newConePlus P p q)
    (oldPositivePlus P p' q') (positiveMovementPlus P p' q')
    (polynomialMovementPlus P p' q') (laurentMovementPlus P p' q')
    (newPositivePlus P p' q') (oldConePlus P p' q') (newConePlus P p' q')
    (rectanglePlus P p q) (rectanglePlus P p' q')
    (coneComparisonPlus P p q) (coneComparisonPlus P p' q')
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ r s
  · intro t
    exact shifted_transport P p q p' q' h _
  · intro t
    exact shifted_transport P p q p' q' h _
  · intro t
    exact shifted_transport P p q p' q' h _
  · intro t
    exact shifted_transport P p q p' q' h _
  · intro t
    exact shifted_transport P p q p' q' h _
  · intro t
    exact coneSquarePlus_transport P p q p' q' h 0 t
  · intro t
    exact coneSquarePlus_transport P p q p' q' h 1 t
  · intro u v
    exact eq_of_heq ((transport_heq P p q p' q' h _).trans
      (rectanglePlus_heq P p q p' q' h u v))
  · intro u v
    rw [coneComparisonPlus_apply, coneComparisonPlus_apply]
    exact coneBoundaryPlus_transport P p q p' q' h u v

end Quillen.PerfectComplexes.CoefficientBassCompositeJ0NullTransport
