/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeJ0Conjugation
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeJ0NullTransport
public import Quillen.Topology.Path.TwoSheetConjugationEvaluation

/-!
# Equal-composite transport of the actual J0 comparison

All full-node primitive maps and original pasted comparisons have already been transported.
The existing literal conjugation recipe therefore commutes with the actual carrier map.
Neither independently chosen cube interiors nor native-value cancellation is used.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassCompositeJ0ConjugationTransport
open CoefficientBassCompositeJ0Rectangles CoefficientBassCompositeJ0PairedNull
open CoefficientBassCompositeJ0RailTransport CoefficientBassCompositeJ0ConeTransport
open CoefficientBassCompositeJ0NullTransport CoefficientBassCompositeJ0TypedUnitRails
open CoefficientBassCompositeJ0Conjugation CoefficientBassNegativeCarrierReference
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b b' c : Under R}
  (p : a ⟶ b) (q : b ⟶ c) (p' : a ⟶ b') (q' : b' ⟶ c)

/-- All original ten-node parameter points commute with actual carrier transport. -/
theorem unit_transport (h : p ≫ q = p' ≫ q') (t : StdSimplex ℝ (Fin 10)) :
    transport P p q p' q' h (CoefficientBassCompositeJ0RectangleRails.unitMap P p q t) =
      CoefficientBassCompositeJ0RectangleRails.unitMap P p' q' t :=
  eq_of_heq ((transport_heq P p q p' q' h _).trans (unit_heq P p q p' q' h t))

/-- The full new minus null word retains its original half cut and tip. -/
theorem newNullMinus_transport (h : p ≫ q = p' ≫ q') (s : I) :
    transport P p q p' q' h (newNullMinus P p q s) = newNullMinus P p' q' s :=
  Path.Evaluation.path_trans (transport P p q p' q' h)
    (newPositiveMinus P p q) (newConeMinus P p q)
    (newPositiveMinus P p' q') (newConeMinus P p' q')
    (fun _ ↦ ordinary_transport P p q p' q' h _)
    (fun t ↦ coneSquareMinus_transport P p q p' q' h 1 t) s

/-- The full new plus null word retains its original half cut and tip. -/
theorem newNullPlus_transport (h : p ≫ q = p' ≫ q') (s : I) :
    transport P p q p' q' h (newNullPlus P p q s) = newNullPlus P p' q' s :=
  Path.Evaluation.path_trans (transport P p q p' q' h)
    (newPositivePlus P p q) (newConePlus P p q)
    (newPositivePlus P p' q') (newConePlus P p' q')
    (fun _ ↦ shifted_transport P p q p' q' h _)
    (fun t ↦ coneSquarePlus_transport P p q p' q' h 1 t) s

/-- The complete original conjugation commutes with transport at both independent times. -/
theorem comparison_transport (h : p ≫ q = p' ≫ q') (r s : I) :
    transport P p q p' q' h (comparison P p q (r, s)) = comparison P p' q' (r, s) := by
  refine Path.Evaluation.twoSheetConjugation (transport P p q p' q' h)
    (oldUnit P p q) (newUnit P p q)
    (laurentMovementMinus P p q) (laurentMovementPlus P p q)
    (oldNullMinus P p q) (oldNullPlus P p q)
    (newNullMinus P p q) (newNullPlus P p q)
    (oldUnit P p' q') (newUnit P p' q')
    (laurentMovementMinus P p' q') (laurentMovementPlus P p' q')
    (oldNullMinus P p' q') (oldNullPlus P p' q')
    (newNullMinus P p' q') (newNullPlus P p' q')
    (unitComparison P p q) (pastedNullMinus P p q) (pastedNullPlus P p q)
    (unitComparison P p' q') (pastedNullMinus P p' q') (pastedNullPlus P p' q')
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ r s
  · intro t
    rw [oldUnit_apply, oldUnit_apply]
    exact unit_transport P p q p' q' h _
  · intro t
    rw [newUnit_apply, newUnit_apply]
    exact unit_transport P p q p' q' h _
  · intro t
    exact ordinary_transport P p q p' q' h _
  · intro t
    exact shifted_transport P p q p' q' h _
  · exact newNullMinus_transport P p q p' q' h
  · exact newNullPlus_transport P p q p' q' h
  · intro u v
    exact eq_of_heq ((transport_heq P p q p' q' h _).trans
      (unitComparison_heq P p q p' q' h u v))
  · exact pastedNullMinus_transport P p q p' q' h
  · exact pastedNullPlus_transport P p q p' q' h

/-- Reversing only comparison time preserves the entire original J0 surface. -/
theorem reverseComparison_transport (h : p ≫ q = p' ≫ q') (r s : I) :
    transport P p q p' q' h (reverseComparison P p q (r, s)) =
      reverseComparison P p' q' (r, s) :=
  comparison_transport P p q p' q' h (unitInterval.symm r) s

end Quillen.PerfectComplexes.CoefficientBassCompositeJ0ConjugationTransport
