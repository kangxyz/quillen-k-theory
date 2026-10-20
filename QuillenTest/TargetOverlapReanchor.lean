/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeTargetOverlapReanchor

/-! # Scalar recovery of the four original clocks and both original H0 chart rows -/

set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.PerfectComplexes
open Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Target
open scoped Simplicial Topology unitInterval

universe u

namespace QuillenTest.TargetOverlapReanchor

open CommonReferenceNerve CommonReferenceProduct ProjectionRectangleParameters

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
  {V : Model.{u + 1}}
  (E E' : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
  (δ : E'.functor ≅ E.functor)

/-- All four distinct original quarter clocks satisfy the same full scalar square. -/
theorem all_original_cells (i : Fin 4)
    (y : |nerve (Codiscrete (CommonReferenceNerve.Node E))|) (s t : I) :
    mapParameter (reanchor (isoWhiskerRight δ (BassH0Diagram.reference P f).functor))
      (cell P f E (![clock12, clock01, clock03, clock34] i) (y, (s, t))) =
    cell P f E' (![clock12, clock01, clock03, clock34] i)
      (mapParameter (reanchor δ) y, (s, t)) :=
  cell_reanchor P f E E' δ _ y s t

/-- The complete original positive chart row, not just its endpoints, survives reanchoring. -/
theorem positive_chart_row
    (y : |nerve (Codiscrete (CommonReferenceNerve.Node E))|) (s : I) :
    mapParameter (reanchor (isoWhiskerRight δ (BassH0Diagram.reference P f).functor))
      (FiniteParameter.parameter E (reference P f E) (nodes P f E)
        (y, L BassH0Diagram.plusFace s)) =
    FiniteParameter.parameter E' (reference P f E') (nodes P f E')
      (mapParameter (reanchor δ) y, L BassH0Diagram.plusFace s) := by
  rw [← overlap_left, ← overlap_left]
  exact overlap_reanchor P f E E' δ y s 0

/-- The inverse chart retains its separate full row and unchanged path time. -/
theorem negative_chart_row
    (y : |nerve (Codiscrete (CommonReferenceNerve.Node E))|) (s : I) :
    mapParameter (reanchor (isoWhiskerRight δ (BassH0Diagram.reference P f).functor))
      (FiniteParameter.parameter E (reference P f E) (nodes P f E)
        (y, L BassH0Diagram.minusFace s)) =
    FiniteParameter.parameter E' (reference P f E') (nodes P f E')
      (mapParameter (reanchor δ) y, L BassH0Diagram.minusFace s) := by
  rw [← overlap_right, ← overlap_right]
  exact overlap_reanchor P f E E' δ y s 1

end QuillenTest.TargetOverlapReanchor
