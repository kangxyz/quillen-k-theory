/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassH0ChartSharedNodes
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassH0MergeIndex

/-! One actual common reference simplex for the supported H0, chart, and bottom faces. -/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassH0Merged
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The representatives use the actual old and H0 nodes, including their original references. -/
def nodes (i : Fin 63) : BassOverlap.Node P u v :=
  Sum.elim (BassReferenceMerge.nodes P u v) (BassH0Merge.nodes P u v) (select i)

/-- Every original old node retains its full dependent data in the new order. -/
theorem old_nodes (i : Fin 45) : nodes P u v (BassSupportOrder.oldIndex i) =
    BassReferenceMerge.nodes P u v i := by
  unfold nodes
  rw [select_old]
  rfl

/-- All H0 nodes retain their full dependent data, using the thirteen proved actual identities. -/
theorem h0_nodes (i : Fin 31) : nodes P u v (BassSupportOrder.h0Index i) =
    BassH0Merge.nodes P u v i := by
  unfold nodes
  rw [select_h0]
  fin_cases i
  · rfl
  · rfl
  · exact (BassH0Merge.shared_source_node P u v).symm
  · exact (BassH0Merge.shared_positive_raw_node P u v).symm
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (BassH0Merge.shared_positive_center_node P u v).symm
  · exact (BassH0Merge.shared_positive_laurent_raw_node P u v).symm
  · exact (BassH0Merge.shared_positive_target_node P u v).symm
  · exact (BassH0Merge.shared_positive_polynomial_raw_node P u v).symm
  · exact (BassH0Merge.shared_positive_polynomial_target_node P u v).symm
  · exact (BassH0Merge.shared_negative_raw_node P u v).symm
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (BassH0Merge.shared_negative_center_node P u v).symm
  · exact (BassH0Merge.shared_negative_laurent_raw_node P u v).symm
  · exact (BassH0Merge.shared_negative_target_node P u v).symm
  · exact (BassH0Merge.shared_negative_polynomial_raw_node P u v).symm
  · exact (BassH0Merge.shared_negative_polynomial_target_node P u v).symm
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-- The actual 62-simplex uses only the original full nodes and their canonical common reference. -/
def simplex : ModelSimplex
    (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
    (modelOf (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj c)))) 62 :=
  ModelSimplex.ofIsos (BassOverlap.commonReference P u v)
    (fun i ↦ (nodes P u v i).1) (fun i ↦ (nodes P u v i).2)

end Quillen.PerfectComplexes.BassH0Merged
