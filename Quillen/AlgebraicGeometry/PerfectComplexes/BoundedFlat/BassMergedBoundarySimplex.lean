/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassSharedNodes

/-! Merge the complete original chart/bottom boundary nodes, retaining all three whole faces. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.PolynomialBaseChange AlgebraicGeometry.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassReferenceMerge

/-- Original 51-slot representatives in a common order preserving all three full face orders. -/
def select (i : Fin 45) : Fin 51 :=
  ⟨if i.val < 15 then i.val else
    if i.val < 21 then i.val + 21 else
      if i.val < 39 then i.val - 6 else
        if i.val < 42 then i.val + 6 else i.val - 9, by
    split_ifs <;> omega⟩

def chartIndex (i : Fin 36) : Fin 45 :=
  ⟨if i.val < 15 then i.val else if i.val < 33 then i.val + 6 else i.val + 9, by
    split_ifs <;> omega⟩

def bottomIndex (i : Fin 15) : Fin 45 :=
  ⟨if i.val < 9 then i.val + 15 else i.val + 30, by split_ifs <;> omega⟩

def chartFace : ⦋35⦌ ⟶ ⦋44⦌ := SimplexCategory.Hom.mk ⟨chartIndex, by
  intro i j hij
  change (chartIndex i).val ≤ (chartIndex j).val
  dsimp [chartIndex]
  split_ifs <;> omega⟩

def bottomFace : ⦋14⦌ ⟶ ⦋44⦌ := SimplexCategory.Hom.mk ⟨bottomIndex, by
  intro i j hij
  change (bottomIndex i).val ≤ (bottomIndex j).val
  dsimp [bottomIndex]
  split_ifs <;> omega⟩

theorem select_chartIndex (i : Fin 36) : select (chartIndex i) = Fin.castAdd 15 i := by
  apply Fin.ext
  dsimp [select, chartIndex]
  split_ifs <;> omega

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- Representatives retain the complete previously frozen reference nodes. -/
def nodes (i : Fin 45) : BassOverlap.Node P u v :=
  BassBottomCommonFamily.nodes P u v (select i)

/-- All six shared full nodes are now identified in one actual 44-simplex. -/
def simplex : ModelSimplex
    (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
    (modelOf (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj c)))) 44 :=
  ModelSimplex.ofIsos (BassOverlap.commonReference P u v)
    (fun i ↦ (nodes P u v i).1) (fun i ↦ (nodes P u v i).2)

theorem chart_nodes (i : Fin 36) : nodes P u v (chartFace.toOrderHom i) =
    BassBottomCommonFamily.nodes P u v (BassBottomCommonFamily.chartFace.toOrderHom i) := by
  unfold nodes
  exact congrArg (BassBottomCommonFamily.nodes P u v) (select_chartIndex i)

/-- Every bottom node is its original full dependent node, including the six shared ones. -/
theorem bottom_nodes (i : Fin 15) : nodes P u v (bottomFace.toOrderHom i) =
    BassBottomCommonFamily.nodes P u v (BassBottomCommonFamily.bottomFace.toOrderHom i) := by
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact plus_source_node P u v
  · exact plus_intermediate_node P u v
  · exact plus_target_node P u v
  · rfl
  · rfl
  · rfl
  · exact minus_source_node P u v
  · exact minus_intermediate_node P u v
  · exact minus_target_node P u v

/-- Both whole fixed chart diagrams remain the original precomposed common-chart simplex. -/
theorem chart_face : (simplex P u v).face chartFace = BassOverlap.simplex P u v := by
  rw [← BassBottomCommonFamily.chart_face P u v]
  unfold simplex BassBottomCommonFamily.simplex
  rw [ModelSimplex.ofIsos_face, ModelSimplex.ofIsos_face]
  exact ModelSimplex.ofIsos_nodes_congr _ _ (chart_nodes P u v)

/-- The whole bottom grid diagram remains the original one, with all internal transformations. -/
theorem bottom_face : (simplex P u v).face bottomFace =
    BassLaurentBottomFace.simplex P u v := by
  rw [← BassBottomCommonFamily.bottom_face P u v]
  unfold simplex BassBottomCommonFamily.simplex
  rw [ModelSimplex.ofIsos_face, ModelSimplex.ofIsos_face]
  exact ModelSimplex.ofIsos_nodes_congr _ _ (bottom_nodes P u v)

end Quillen.PerfectComplexes.BassReferenceMerge
