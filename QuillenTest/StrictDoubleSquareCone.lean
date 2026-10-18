/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.Prespectrum.StrictDoubleSquareConeNaturality
public import Quillen.Topology.Prespectrum.StrictDoubleSquareConeCells

/-!
# Regression for the original double-total-cone interchange

The actual inverse recovers the original map of any strict four-dimensional
diagram. On the deepest quotient cell all four independent parameters survive
that transport. The specified inverse also reverses the complete block swap.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen Quillen.LoopPrespectrum
open Quillen.LoopPrespectrum.StrictSquare
open Quillen.LoopPrespectrum.StrictSquare.Double
open scoped Topology unitInterval
universe u
namespace QuillenTest.StrictDoubleSquareCone
variable {E E' : Arrow (Arrow (Arrow (Arrow LoopPrespectrum.{u})))} (h : E ⟶ E')

/-- Conjugation recovers the given original map of the two total cones. -/
theorem conjugation_recovers_map :
    (interchangeIso E).hom ≫ totalFunctor.map (coneSquareMap (comparisonArrowMap h)) ≫
        (interchangeIso E').inv =
      totalFunctor.map (totalFunctor.mapArrow.mapArrow.map h) := by
  rw [← Category.assoc, ← interchangeIso_naturality, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- Four independent original cell parameters survive the entire natural round trip. -/
theorem transported_four_parameters (n : ℕ) (r s t v : unitInterval)
    (x : E.left.left.left.left.space n) :
    ((interchangeIso E).hom ≫ totalFunctor.map (coneSquareMap (comparisonArrowMap h)) ≫
      (interchangeIso E').inv).map n
        (Cell.overlap (totalFunctor.mapArrow.mapArrow.obj E) n r s
          (Cell.overlap E.left.left n t v x)) =
      Cell.overlap (totalFunctor.mapArrow.mapArrow.obj E') n r s
        (Cell.overlap E'.left.left n t v (h.left.left.left.left.map n x)) := by
  rw [conjugation_recovers_map]
  rfl

/-- The specified inverse returns the complete swapped four-parameter cell unchanged. -/
theorem inverse_four_parameters (n : ℕ) (r s t v : unitInterval)
    (x : E.left.left.left.left.space n) :
    (interchangeIso E).inv.map n
      (Cell.overlap (coneSquare (comparisonMap E)) n t v
        (Cell.overlap ((Arrow.leftFunc ⋙ Arrow.leftFunc).mapArrow.mapArrow.obj E) n r s x)) =
      Cell.overlap (totalFunctor.mapArrow.mapArrow.obj E) n r s
        (Cell.overlap E.left.left n t v x) := by
  rw [← interchange_overlap_overlap]
  exact congrArg (fun k => k.map n
    (Cell.overlap (totalFunctor.mapArrow.mapArrow.obj E) n r s
      (Cell.overlap E.left.left n t v x))) (interchangeIso E).hom_inv_id

#print axioms comparisonMap
#print axioms sourceIso_comparison
#print axioms comparisonArrowIso
#print axioms interchangeIso
#print axioms interchangeIso_naturality
#print axioms interchangeIso_inv_naturality
#print axioms interchange_overlap_overlap
#print axioms transported_four_parameters
#print axioms inverse_four_parameters

end QuillenTest.StrictDoubleSquareCone
