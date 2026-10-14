/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.DoubleSquareSharedNodes
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.DoubleSquareNativeLifts

/-! The three native double-square triples with their actual shared nodes identified. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Convexity
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.DoubleSquareMergedSimplex
variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)

/-- Representatives ordered so that all three original eight-vertex diagrams remain faces. -/
def select : Fin 18 → Fin 24 := ![0, 1, 2, 3, 9, 10, 11, 19, 4, 5, 6, 7, 14, 15, 20, 21, 22, 23]

def nodes (i : Fin 18) : DoubleSquareCommonSimplex.Node p q c :=
  DoubleSquareCommonSimplex.nodes p q p' q' a b c hp hq (select i)

/-- The actual 17-simplex uses the original nodes and proven common reference equations. -/
def simplex : ModelSimplex (modelOf (boundedFlatPerfectWaldhausen A))
    (modelOf (boundedFlatPerfectWaldhausen C')) 17 :=
  ModelSimplex.ofIsos (NormalizedTripleSimplex.sourceMap c q p)
    (fun i ↦ (nodes p q p' q' a b c hp hq i).1)
    (fun i ↦ (nodes p q p' q' a b c hp hq i).2)

def firstFace : ⦋7⦌ ⟶ ⦋17⦌ :=
  SimplexCategory.Hom.mk ⟨![0, 1, 2, 3, 8, 9, 10, 11], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩

def middleFace : ⦋7⦌ ⟶ ⦋17⦌ :=
  SimplexCategory.Hom.mk ⟨![0, 4, 5, 6, 8, 9, 12, 13], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩

def lastFace : ⦋7⦌ ⟶ ⦋17⦌ :=
  SimplexCategory.Hom.mk ⟨![0, 4, 5, 7, 14, 15, 16, 17], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩

theorem first_nodes (i : Fin 8) : nodes p q p' q' a b c hp hq (firstFace.toOrderHom i) =
    DoubleSquareCommonSimplex.nodes p q p' q' a b c hp hq
      (DoubleSquareCommonSimplex.firstFace.toOrderHom i) := by
  unfold nodes
  apply congrArg (DoubleSquareCommonSimplex.nodes p q p' q' a b c hp hq)
  fin_cases i <;> rfl

theorem middle_nodes (i : Fin 8) : nodes p q p' q' a b c hp hq (middleFace.toOrderHom i) =
    DoubleSquareCommonSimplex.nodes p q p' q' a b c hp hq
      (DoubleSquareCommonSimplex.middleFace.toOrderHom i) := by
  fin_cases i
  · exact DoubleSquareCommonSimplex.source_middle_shared p q p' q' a b c hp hq
  · rfl
  · rfl
  · rfl
  · exact DoubleSquareCommonSimplex.right_raw_shared p q p' q' a b c hp hq
  · exact DoubleSquareCommonSimplex.right_normalized_shared p q p' q' a b c hp hq
  · rfl
  · rfl

theorem last_nodes (i : Fin 8) : nodes p q p' q' a b c hp hq (lastFace.toOrderHom i) =
    DoubleSquareCommonSimplex.nodes p q p' q' a b c hp hq
      (DoubleSquareCommonSimplex.lastFace.toOrderHom i) := by
  fin_cases i
  · exact DoubleSquareCommonSimplex.source_last_shared p q p' q' a b c hp hq
  · exact DoubleSquareCommonSimplex.left_raw_shared p q p' q' a b c hp hq
  · exact DoubleSquareCommonSimplex.left_normalized_shared p q p' q' a b c hp hq
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-- The whole first old split triple is retained after identifying the shared nodes. -/
theorem first_face : (simplex p q p' q' a b c hp hq).face firstFace =
    SplitTripleSimplex.simplex c q p := by
  rw [← DoubleSquareCommonSimplex.first_face p q p' q' a b c hp hq]
  unfold simplex DoubleSquareCommonSimplex.simplex
  rw [ModelSimplex.ofIsos_face, ModelSimplex.ofIsos_face]
  exact ModelSimplex.ofIsos_nodes_congr _ _ (first_nodes p q p' q' a b c hp hq)

/-- The middle old split triple shares its actual first intermediate with the first face. -/
theorem middle_face : (simplex p q p' q' a b c hp hq).face middleFace =
    SplitTripleSimplex.simplex q' b p := by
  rw [← DoubleSquareCommonSimplex.middle_face p q p' q' a b c hp hq]
  unfold simplex DoubleSquareCommonSimplex.simplex
  rw [ModelSimplex.ofIsos_face, ModelSimplex.ofIsos_face]
  exact ModelSimplex.ofIsos_nodes_congr _ _ (middle_nodes p q p' q' a b c hp hq)

/-- The last old split triple shares the actual middle total with the middle face. -/
theorem last_face : (simplex p q p' q' a b c hp hq).face lastFace =
    SplitTripleSimplex.simplex q' p' a := by
  rw [← DoubleSquareCommonSimplex.last_face p q p' q' a b c hp hq]
  unfold simplex DoubleSquareCommonSimplex.simplex
  rw [ModelSimplex.ofIsos_face, ModelSimplex.ofIsos_face]
  exact ModelSimplex.ofIsos_nodes_congr _ _ (last_nodes p q p' q' a b c hp hq)

end Quillen.PerfectComplexes.DoubleSquareMergedSimplex
