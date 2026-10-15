/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeSelection

/-! The concrete common 139-simplex retains every original full dependent reference node. -/
@[expose] public section

open Quillen.PerfectComplexes.BassMWholeOrder

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassMWhole
open BassMWholeOrder
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- Every chosen node is an unchanged input node with its full reference iso. -/
def nodes (i : Fin 140) : BassOverlap.Node P u v := inputNode P u v (selection i)

/-- All 131 original five-face nodes retain their full original references. -/
theorem old_nodes (i : Fin 131) : nodes P u v (oldIndex i) = BassH1Merged.nodes P u v i := by
  unfold nodes
  rw [selection_old]
  exact input_old P u v i

/-- All 45 first-stage nodes survive through the proved full boundary identifications. -/
theorem vertex_nodes (i : Fin 45) : nodes P u v (vertexIndex i) = BassMVertex.nodes P u v i := by
  unfold nodes
  rw [selection_vertex]
  fin_cases i
  · exact (input_old P u v 3).trans
      (BassMOuterJoin.source_plus_nodes P u v 0).symm
  · exact (input_old P u v 5).trans
      (BassMOuterJoin.source_plus_nodes P u v 3).symm
  · exact (input_old P u v 11).trans
      (BassMOuterJoin.source_middle_nodes P u v 0).symm
  · exact (input_old P u v 12).trans
      (BassMOuterJoin.source_middle_nodes P u v 1).symm
  · exact (input_old P u v 13).trans
      (BassMOuterJoin.source_plus_nodes P u v 4).symm
  · exact (input_old P u v 14).trans
      (BassMOuterJoin.source_middle_nodes P u v 3).symm
  · exact (input_old P u v 7).trans
      (BassMOuterJoin.source_minus_nodes P u v 0).symm
  · exact (input_old P u v 9).trans
      (BassMOuterJoin.source_minus_nodes P u v 3).symm
  · exact (input_old P u v 15).trans
      (BassMOuterJoin.source_middle_nodes P u v 4).symm
  · exact input_vertex P u v 9
  · exact input_vertex P u v 10
  · exact input_vertex P u v 11
  · exact input_vertex P u v 12
  · exact (input_old P u v 52).trans
      (BassMOuterJoin.boundary_first_plus_nodes P u v 0).symm
  · exact (input_old P u v 85).trans
      (BassMOuterJoin.boundary_first_plus_nodes P u v 3).symm
  · exact (input_old P u v 78).trans
      (BassMOuterJoin.boundary_first_plus_nodes P u v 1).symm
  · exact input_vertex P u v 16
  · exact (input_old P u v 35).trans
      (BassMOuterJoin.boundary_second_plus_nodes P u v 0).symm
  · exact (input_old P u v 37).trans
      (BassMOuterJoin.boundary_second_plus_nodes P u v 3).symm
  · exact input_vertex P u v 19
  · exact input_vertex P u v 20
  · exact (input_old P u v 43).trans
      (BassMOuterJoin.boundary_middle_nodes P u v 0).symm
  · exact (input_old P u v 44).trans
      (BassMOuterJoin.boundary_middle_nodes P u v 1).symm
  · exact (input_old P u v 45).trans
      (BassMOuterJoin.boundary_second_plus_nodes P u v 4).symm
  · exact (input_old P u v 36).trans
      (BassMOuterJoin.boundary_second_plus_nodes P u v 1).symm
  · exact (input_old P u v 122).trans
      (BassMOuterJoin.boundary_first_plus_nodes P u v 4).symm
  · exact (input_old P u v 4).trans
      (BassMOuterJoin.source_plus_nodes P u v 1).symm
  · exact (input_old P u v 25).trans
      (BassMOuterJoin.source_plus_nodes P u v 2).symm
  · exact (input_old P u v 26).trans
      (BassMOuterJoin.boundary_side_plus_nodes P u v 1).symm
  · exact (input_old P u v 80).trans
      (BassMOuterJoin.boundary_side_plus_nodes P u v 2).symm
  · exact (input_old P u v 46).trans
      (BassMOuterJoin.boundary_middle_nodes P u v 3).symm
  · exact input_vertex P u v 31
  · exact (input_old P u v 90).trans
      (BassMOuterJoin.boundary_first_minus_nodes P u v 0).symm
  · exact (input_old P u v 128).trans
      (BassMOuterJoin.boundary_first_minus_nodes P u v 3).symm
  · exact (input_old P u v 107).trans
      (BassMOuterJoin.boundary_first_minus_nodes P u v 1).symm
  · exact input_vertex P u v 35
  · exact (input_old P u v 39).trans
      (BassMOuterJoin.boundary_second_minus_nodes P u v 0).symm
  · exact (input_old P u v 41).trans
      (BassMOuterJoin.boundary_second_minus_nodes P u v 3).symm
  · exact (input_old P u v 47).trans
      (BassMOuterJoin.boundary_second_minus_nodes P u v 4).symm
  · exact (input_old P u v 40).trans
      (BassMOuterJoin.boundary_second_minus_nodes P u v 1).symm
  · exact (input_old P u v 130).trans
      (BassMOuterJoin.boundary_first_minus_nodes P u v 4).symm
  · exact (input_old P u v 8).trans
      (BassMOuterJoin.source_minus_nodes P u v 1).symm
  · exact (input_old P u v 69).trans
      (BassMOuterJoin.source_minus_nodes P u v 2).symm
  · exact (input_old P u v 70).trans
      (BassMOuterJoin.boundary_side_minus_nodes P u v 1).symm
  · exact (input_old P u v 109).trans
      (BassMOuterJoin.boundary_side_minus_nodes P u v 2).symm

/-- The common family uses these unchanged nodes and the original common reference. -/
def simplex := BassMFamilyTransfer.nativeSimplex P u v (nodes P u v)

end Quillen.PerfectComplexes.BassMWhole
