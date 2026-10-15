/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MVertexMergeIndex

/-! One actual 44-simplex containing all three whole original M vertex-stage diagrams. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.PolynomialBaseChange AlgebraicGeometry.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassMVertex
open BassMComponents BassMReferences BassMVertexOrder
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- Every input is one of the unchanged original moving or product full reference nodes. -/
def inputNode (i : Fin 51) : BassOverlap.Node P u v :=
  Fin.addCases (m := 18) (n := 33) (motive := fun _ ↦ BassOverlap.Node P u v)
    (movingNodes P u v (underToLaurent R) (laurentPlus_projection P c))
    (fun j ↦ Fin.addCases (m := 15) (n := 18) (motive := fun _ ↦ BassOverlap.Node P u v)
      (middleNodes P u v)
      (movingNodes P u v (underToLaurentInvert R) (laurentMinus_projection P c)) j) i

/-- Representatives are selected after proving the six full dependent node equalities. -/
def nodes (i : Fin 45) : BassOverlap.Node P u v := inputNode P u v (select i)

/-- Every complete original positive moving-square node is retained. -/
theorem plus_nodes (i : Fin 18) : nodes P u v (plusIndex i) =
    movingNodes P u v (underToLaurent R) (laurentPlus_projection P c) i := by
  fin_cases i <;> rfl

/-- Every original middle product node is retained, with the actual shared positive references. -/
theorem middle_nodes (i : Fin 15) : nodes P u v (middleIndex i) = middleNodes P u v i := by
  fin_cases i
  · rfl
  · rfl
  · exact BassMJoin.plus_internal_nodes P u v 0
  · rfl
  · rfl
  · rfl
  · rfl
  · exact BassMJoin.plus_internal_nodes P u v 1
  · rfl
  · rfl
  · rfl
  · rfl
  · exact BassMJoin.plus_internal_nodes P u v 2
  · rfl
  · rfl

/-- The inverse diagram retains all original nodes and their separate inverse references. -/
theorem minus_nodes (i : Fin 18) : nodes P u v (minusIndex i) =
    movingNodes P u v (underToLaurentInvert R) (laurentMinus_projection P c) i := by
  fin_cases i
  · rfl
  · rfl
  · exact (BassMJoin.minus_internal_nodes P u v 0).symm
  · exact (BassMJoin.minus_internal_nodes P u v 1).symm
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (BassMJoin.minus_internal_nodes P u v 2).symm
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-- The actual common family contains all original constituent diagrams as whole simplex faces. -/
def simplex := ModelSimplex.ofIsos (BassOverlap.commonReference P u v)
  (fun i ↦ (nodes P u v i).1) (fun i ↦ (nodes P u v i).2)

theorem plus_face : (simplex P u v).face plusFace = plusSimplex P u v := by
  unfold simplex
  rw [ModelSimplex.ofIsos_face]
  exact (ModelSimplex.ofIsos_nodes_congr _ _ (plus_nodes P u v)).trans
    (moving_original P u v (underToLaurent R) (laurentPlus_projection P c))

theorem middle_face : (simplex P u v).face middleFace = middleSimplex P u v := by
  unfold simplex
  rw [ModelSimplex.ofIsos_face]
  exact (ModelSimplex.ofIsos_nodes_congr _ _ (middle_nodes P u v)).trans
    (middle_original P u v)

theorem minus_face : (simplex P u v).face minusFace = minusSimplex P u v := by
  unfold simplex
  rw [ModelSimplex.ofIsos_face]
  exact (ModelSimplex.ofIsos_nodes_congr _ _ (minus_nodes P u v)).trans
    (moving_original P u v (underToLaurentInvert R) (laurentMinus_projection P c))

end Quillen.PerfectComplexes.BassMVertex
