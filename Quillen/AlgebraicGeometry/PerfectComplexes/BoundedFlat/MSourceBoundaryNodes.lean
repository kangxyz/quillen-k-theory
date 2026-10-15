/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MSourcePolynomialRows
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MSourceMiddleRows

/-! The full original source-M/H0 boundary in the fixed first-stage and H1 node families. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.PolynomialBaseChange AlgebraicGeometry.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassMOuterJoin
open BassH0Merge BassH1Join BassMComponents BassMReferences

/-- Actual first-stage node labels of the whole source positive path. -/
def sourcePlusIndex (i : Fin 5) : Fin 45 := BassMVertexOrder.plusIndex (movingSourceWordIndex i)
/-- Actual first-stage node labels of the whole source middle path. -/
def sourceMiddleIndex (i : Fin 5) : Fin 45 :=
  BassMVertexOrder.middleIndex (Quillen.SimplexGrid.index 2 4 (0, i))
/-- Actual first-stage node labels of the separate source inverse path. -/
def sourceMinusIndex (i : Fin 5) : Fin 45 := BassMVertexOrder.minusIndex (movingSourceWordIndex i)

/-- The unchanged fixed-family labels of H0's whole target positive path. -/
def oldSourcePlusIndex (i : Fin 5) : Fin 131 :=
  BassH1Order.oldIndex (BassSupportOrder.h0Index
    (BassH0Diagram.plusFace.toOrderHom (polynomialWordIndex i)))
/-- The unchanged fixed-family labels of H0's whole target middle path. -/
def oldSourceMiddleIndex (i : Fin 5) : Fin 131 :=
  BassH1Order.oldIndex (BassSupportOrder.h0Index (firstMiddleFace.toOrderHom i))
/-- The unchanged fixed-family labels of H0's separate target inverse path. -/
def oldSourceMinusIndex (i : Fin 5) : Fin 131 :=
  BassH1Order.oldIndex (BassSupportOrder.h0Index
    (BassH0Diagram.minusFace.toOrderHom (polynomialWordIndex i)))

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The complete positive source path retains the original full H0 target references. -/
theorem source_plus_h0_nodes (i : Fin 5) :
    movingNodes P u v (underToLaurent R) (laurentPlus_projection P c) (movingSourceWordIndex i) =
    BassH0Merge.nodes P u v (BassH0Diagram.plusFace.toOrderHom (polynomialWordIndex i)) := by
  have hn := source_polynomial_word_nodes P u v (underToLaurent R)
    (laurentPlus_projection P a) (laurentPlus_projection P c) i
  have hp := congrArg (anchorNode (F₀ := BassOverlap.commonReference P u v)
    (F₁ := BassH0Diagram.reference P (u ≫ v)) (eqToIso (reference_eq P u v)))
      (BassH0Diagram.plus_nodes P (u ≫ v) (polynomialWordIndex i))
  exact hn.trans hp.symm

/-- The complete inverse source path retains its separate original H0 target references. -/
theorem source_minus_h0_nodes (i : Fin 5) :
    movingNodes P u v (underToLaurentInvert R) (laurentMinus_projection P c)
      (movingSourceWordIndex i) =
    BassH0Merge.nodes P u v (BassH0Diagram.minusFace.toOrderHom (polynomialWordIndex i)) := by
  have hn := source_polynomial_word_nodes P u v (underToLaurentInvert R)
    (laurentMinus_projection P a) (laurentMinus_projection P c) i
  have hp := congrArg (anchorNode (F₀ := BassOverlap.commonReference P u v)
    (F₁ := BassH0Diagram.reference P (u ≫ v)) (eqToIso (reference_eq P u v)))
      (BassH0Diagram.minus_nodes P (u ≫ v) (polynomialWordIndex i))
  exact hn.trans hp.symm

/-- Every positive path node is shared literally by the fixed first-stage and five-face families. -/
theorem source_plus_nodes (i : Fin 5) :
    BassMVertex.nodes P u v (sourcePlusIndex i) =
      BassH1Merged.nodes P u v (oldSourcePlusIndex i) :=
  (BassMVertex.plus_nodes P u v _).trans ((source_plus_h0_nodes P u v i).trans
    ((BassH0Merged.h0_nodes P u v _).symm.trans (BassH1Merged.old_nodes P u v _).symm))

/-- Every middle path node is shared literally, including both distinct raw projection nodes. -/
theorem source_middle_nodes (i : Fin 5) :
    BassMVertex.nodes P u v (sourceMiddleIndex i) =
      BassH1Merged.nodes P u v (oldSourceMiddleIndex i) :=
  (BassMVertex.middle_nodes P u v _).trans ((source_middle_path_nodes P u v i).trans
    ((BassH0Merged.h0_nodes P u v _).symm.trans (BassH1Merged.old_nodes P u v _).symm))

/-- The inverse full nodes are shared with the correct separate chart of the fixed family. -/
theorem source_minus_nodes (i : Fin 5) :
    BassMVertex.nodes P u v (sourceMinusIndex i) =
      BassH1Merged.nodes P u v (oldSourceMinusIndex i) :=
  (BassMVertex.minus_nodes P u v _).trans ((source_minus_h0_nodes P u v i).trans
    ((BassH0Merged.h0_nodes P u v _).symm.trans (BassH1Merged.old_nodes P u v _).symm))

end Quillen.PerfectComplexes.BassMOuterJoin
