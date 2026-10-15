/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MTargetMiddleNodes

/-! Actual complete boundary node identifications between the fixed 44- and 130-simplex families. -/
@[expose] public section

open Quillen.PerfectComplexes.BassH0Merge
open Quillen.PerfectComplexes.BassH1Join
open Quillen.PerfectComplexes.BassMComponents
open Quillen.PerfectComplexes.BassMReferences

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassMOuterJoin
open BassH0Merge BassH1Join BassMComponents BassMReferences

/-- Locates the three positive moving-side nodes in the 45-node M family. -/
def sidePlusIndex (i : Fin 3) : Fin 45 :=
  BassMVertexOrder.plusIndex (DoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i))
/-- Locates the matching positive old chart-side nodes in the merged 131-node H1 family. -/
def oldSidePlusIndex (i : Fin 3) : Fin 131 :=
  BassH1Order.oldIndex (BassSupportOrder.oldIndex (BassReferenceMerge.chartFace.toOrderHom
    (BassOverlap.plusFace.toOrderHom
      (DoubleSquareMergedSimplex.firstFace.toOrderHom (leftIndex i)))))
/-- Locates the five vertices of the positive first target word in the M family. -/
def targetFirstPlusIndex (i : Fin 5) : Fin 45 :=
  BassMVertexOrder.plusIndex (firstTargetWordIndex i)
/-- Locates the matching last-column nodes of the positive H1 product grid in the merged family. -/
def oldTargetFirstPlusIndex (i : Fin 5) : Fin 131 :=
  BassH1Order.plusProductIndex (Quillen.SimplexGrid.index 4 4 (i, 4))
/-- Locates the five vertices of the positive second target word in the M family. -/
def targetSecondPlusIndex (i : Fin 5) : Fin 45 :=
  BassMVertexOrder.plusIndex (secondTargetWordIndex i)
/--
Locates the matching positive polynomial-path nodes of the middle H1 component in the merged
family.
-/
def oldTargetSecondPlusIndex (i : Fin 5) : Fin 131 :=
  BassH1Order.middleIndex (BassH0Diagram.plusFace.toOrderHom (polynomialWordIndex i))

/-- Locates the three inverse moving-side nodes in the 45-node M family. -/
def sideMinusIndex (i : Fin 3) : Fin 45 :=
  BassMVertexOrder.minusIndex (DoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i))
/-- Locates the matching inverse old chart-side nodes in the merged 131-node H1 family. -/
def oldSideMinusIndex (i : Fin 3) : Fin 131 :=
  BassH1Order.oldIndex (BassSupportOrder.oldIndex (BassReferenceMerge.chartFace.toOrderHom
    (BassOverlap.minusFace.toOrderHom
      (DoubleSquareMergedSimplex.firstFace.toOrderHom (leftIndex i)))))
/-- Locates the five vertices of the inverse first target word in the M family. -/
def targetFirstMinusIndex (i : Fin 5) : Fin 45 :=
  BassMVertexOrder.minusIndex (firstTargetWordIndex i)
/-- Locates the matching last-column nodes of the inverse H1 product grid in the merged family. -/
def oldTargetFirstMinusIndex (i : Fin 5) : Fin 131 :=
  BassH1Order.minusProductIndex (Quillen.SimplexGrid.index 4 4 (i, 4))
/-- Locates the five vertices of the inverse second target word in the M family. -/
def targetSecondMinusIndex (i : Fin 5) : Fin 45 :=
  BassMVertexOrder.minusIndex (secondTargetWordIndex i)
/--
Locates the matching inverse polynomial-path nodes of the middle H1 component in the merged
family.
-/
def oldTargetSecondMinusIndex (i : Fin 5) : Fin 131 :=
  BassH1Order.middleIndex (BassH0Diagram.minusFace.toOrderHom (polynomialWordIndex i))

/-- Locates the five target-middle nodes in the final coefficient row of the M middle grid. -/
def targetMiddleIndex (i : Fin 5) : Fin 45 :=
  BassMVertexOrder.middleIndex (Quillen.SimplexGrid.index 2 4 (2, i))
/--
Reindexes the five vertices of `firstMiddleFace` in the middle H1 component's merged
coordinates.
-/
def oldTargetMiddleIndex (i : Fin 5) : Fin 131 :=
  BassH1Order.middleIndex (firstMiddleFace.toOrderHom i)

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- Every original plus side node is literally shared by the two fixed reference families. -/
theorem boundary_side_plus_nodes (i : Fin 3) :
    BassMVertex.nodes P u v (sidePlusIndex i) =
      BassH1Merged.nodes P u v (oldSidePlusIndex i) :=
  (BassMVertex.plus_nodes P u v _).trans ((plus_side_nodes P u v i).trans
    ((old_plus_node P u v _).symm.trans ((BassH0Merged.old_nodes P u v _).symm.trans
      (BassH1Merged.old_nodes P u v _).symm)))

/-- Every full plus first target-path node is literally shared with the original H1 product. -/
theorem boundary_first_plus_nodes (i : Fin 5) :
    BassMVertex.nodes P u v (targetFirstPlusIndex i) =
      BassH1Merged.nodes P u v (oldTargetFirstPlusIndex i) :=
  (BassMVertex.plus_nodes P u v _).trans ((plus_first_target_word_nodes P u v i).trans
    (BassH1Merged.plus_nodes P u v _).symm)

/-- Every full plus second target-path node retains H1's original middle-family reference. -/
theorem boundary_second_plus_nodes (i : Fin 5) :
    BassMVertex.nodes P u v (targetSecondPlusIndex i) =
      BassH1Merged.nodes P u v (oldTargetSecondPlusIndex i) :=
  (BassMVertex.plus_nodes P u v _).trans ((plus_second_target_word_nodes P u v i).trans
    ((h1_middle_plus_nodes P u v _).symm.trans (BassH1Merged.middle_nodes P u v _).symm))

/-- Every original minus side node is literally shared by the two fixed reference families. -/
theorem boundary_side_minus_nodes (i : Fin 3) :
    BassMVertex.nodes P u v (sideMinusIndex i) =
      BassH1Merged.nodes P u v (oldSideMinusIndex i) :=
  (BassMVertex.minus_nodes P u v _).trans ((minus_side_nodes P u v i).trans
    ((old_minus_node P u v _).symm.trans ((BassH0Merged.old_nodes P u v _).symm.trans
      (BassH1Merged.old_nodes P u v _).symm)))

/-- Every full minus first target-path node is literally shared with the original H1 product. -/
theorem boundary_first_minus_nodes (i : Fin 5) :
    BassMVertex.nodes P u v (targetFirstMinusIndex i) =
      BassH1Merged.nodes P u v (oldTargetFirstMinusIndex i) :=
  (BassMVertex.minus_nodes P u v _).trans ((minus_first_target_word_nodes P u v i).trans
    (BassH1Merged.minus_nodes P u v _).symm)

/-- Every full minus second target-path node retains H1's original middle-family reference. -/
theorem boundary_second_minus_nodes (i : Fin 5) :
    BassMVertex.nodes P u v (targetSecondMinusIndex i) =
      BassH1Merged.nodes P u v (oldTargetSecondMinusIndex i) :=
  (BassMVertex.minus_nodes P u v _).trans ((minus_second_target_word_nodes P u v i).trans
    ((h1_middle_minus_nodes P u v _).symm.trans (BassH1Merged.middle_nodes P u v _).symm))

/-- All full central projection-path nodes are shared at the original inter-stage boundary. -/
theorem boundary_middle_nodes (i : Fin 5) :
    BassMVertex.nodes P u v (targetMiddleIndex i) =
      BassH1Merged.nodes P u v (oldTargetMiddleIndex i) :=
  (BassMVertex.middle_nodes P u v _).trans ((target_middle_path_nodes P u v i).trans
    (BassH1Merged.middle_nodes P u v _).symm)

end Quillen.PerfectComplexes.BassMOuterJoin
