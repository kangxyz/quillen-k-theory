/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1MergeIndex

/-! One actual common reference simplex from the original nodes and their proved full joins. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.Waldhausen.IteratedS
open Quillen.PolynomialBaseChange AlgebraicGeometry.Scheme.CoefficientBaseChange
universe u
namespace Quillen.PerfectComplexes.BassH1Merged
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- Every representative is an unchanged original full dependent node. -/
def nodes (i : Fin 131) : BassOverlap.Node P u v := inputNode P u v (select i)

theorem old_nodes (i : Fin 63) : nodes P u v (BassH1Order.oldIndex i) =
    BassH0Merged.nodes P u v i := by
  unfold nodes
  rw [select_old]
  rfl

/-- The original first component retains all complete nodes in the common family. -/
theorem first_nodes (i : Fin 31) :
    nodes P u v (BassH1Order.firstIndex i) =
      BassH1References.firstNodes P u v i := by
  change inputNode P u v (select (BassH1Order.firstIndex i)) = inputNode P u v (firstInput i)
  rw [select_first]
  fin_cases i
  · rfl
  · rfl
  · exact (pair5_nodes P u v 0).symm
  · exact (pair5_nodes P u v 1).symm
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (pair6_nodes P u v 0).symm
  · exact (pair6_nodes P u v 1).symm
  · exact (pair5_nodes P u v 2).symm
  · exact (pair6_nodes P u v 3).symm
  · exact (pair6_nodes P u v 4).symm
  · exact (pair5_nodes P u v 3).symm
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (pair7_nodes P u v 0).symm
  · exact (pair7_nodes P u v 1).symm
  · exact (pair5_nodes P u v 4).symm
  · exact (pair7_nodes P u v 3).symm
  · exact (pair7_nodes P u v 4).symm
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-- The original middle component retains all complete nodes in the common family. -/
theorem middle_nodes (i : Fin 31) :
    nodes P u v (BassH1Order.middleIndex i) =
      BassH1References.middleNodes P u v i := by
  change inputNode P u v (select (BassH1Order.middleIndex i)) = inputNode P u v (middleInput i)
  rw [select_middle]
  fin_cases i
  · rfl
  · rfl
  · exact (pair0_nodes P u v 0)
  · exact (pair0_nodes P u v 1)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (pair0_nodes P u v 2)
  · rfl
  · rfl
  · exact (pair0_nodes P u v 3)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (pair0_nodes P u v 4)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-- The original plus component retains all complete nodes in the common family. -/
theorem plus_nodes (i : Fin 25) :
    nodes P u v (BassH1Order.plusProductIndex i) =
      BassH1References.chartNodes P u v (underToLaurent R)
        (laurentPlus_projection P b) i := by
  change inputNode P u v (select (BassH1Order.plusProductIndex i)) = inputNode P u v (plusInput i)
  rw [select_plus]
  fin_cases i
  · rfl
  · rfl
  · exact (pair1_nodes P u v 0)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (pair1_nodes P u v 1)
  · rfl
  · rfl
  · exact (pair8_nodes P u v 0).symm
  · exact (pair8_nodes P u v 1).symm
  · exact (pair8_nodes P u v 2).symm
  · exact (pair8_nodes P u v 3).symm
  · exact (pair8_nodes P u v 4).symm
  · rfl
  · rfl
  · exact (pair1_nodes P u v 3)
  · rfl
  · rfl
  · exact (pair3_nodes P u v 0)
  · exact (pair3_nodes P u v 1)
  · exact (pair1_nodes P u v 4)
  · exact (pair3_nodes P u v 3)
  · exact (pair3_nodes P u v 4)

/-- The original minus component retains all complete nodes in the common family. -/
theorem minus_nodes (i : Fin 25) :
    nodes P u v (BassH1Order.minusProductIndex i) =
      BassH1References.chartNodes P u v (underToLaurentInvert R)
        (laurentMinus_projection P b) i := by
  change inputNode P u v (select (BassH1Order.minusProductIndex i)) = inputNode P u v (minusInput i)
  rw [select_minus]
  fin_cases i
  · rfl
  · rfl
  · exact (pair2_nodes P u v 0)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (pair2_nodes P u v 1)
  · rfl
  · rfl
  · exact (pair9_nodes P u v 0).symm
  · exact (pair9_nodes P u v 1).symm
  · exact (pair9_nodes P u v 2).symm
  · exact (pair9_nodes P u v 3).symm
  · exact (pair9_nodes P u v 4).symm
  · rfl
  · rfl
  · exact (pair2_nodes P u v 3)
  · rfl
  · rfl
  · exact (pair4_nodes P u v 0)
  · exact (pair4_nodes P u v 1)
  · exact (pair2_nodes P u v 4)
  · exact (pair4_nodes P u v 3)
  · exact (pair4_nodes P u v 4)

/-- The whole 130-simplex is constructed from the original nodes and actual common reference. -/
def simplex : ModelSimplex
    (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
    (modelOf (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj c)))) 130 :=
  ModelSimplex.ofIsos (BassOverlap.commonReference P u v)
    (fun i ↦ (nodes P u v i).1) (fun i ↦ (nodes P u v i).2)

end Quillen.PerfectComplexes.BassH1Merged
