/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassUnitHZeroNodes
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientPolynomialSpanUnitTop
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassUnitSupportOrder
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedReferenceReindex

/-! The forty-eight actual common-reference nodes for the original Bass unit faces.
Every overlap is a proved equality of dependent nodes, including the reference isomorphism.
The whole top embeds monotonically; the sides, bottom and H0 are transported only on their
ordered primitive supports. This module does not assert scalar support coverage or a unit cube. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Simplicial
universe u

namespace Quillen.PerfectComplexes.CoefficientBassUnitNodes
open CoefficientPolynomialSpanUnitNodes CoefficientBassUnitBoundaryNodes
open CoefficientBassUnitHZeroNodes CoefficientBassUnitSupportOrder

variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- Actual representatives for the finite support order, all with the same original reference. -/
def nodes : Fin 48 → Node P a :=
  ![h0Nodes P a 0, h0Nodes P a 1, bottomNodes P a 0, bottomNodes P a 1,
    bottomNodes P a 3, bottomNodes P a 9, h0Nodes P a 4, h0Nodes P a 15,
    plusNodes P a 0, plusNodes P a 1, h0Nodes P a 8, plusSideNodes P a 0,
    plusSideNodes P a 1, plusSideNodes P a 4, plusNodes P a 2, plusNodes P a 3,
    plusNodes P a 4, minusNodes P a 0, minusNodes P a 1, h0Nodes P a 19,
    minusSideNodes P a 0, minusSideNodes P a 1, minusSideNodes P a 4, minusNodes P a 2,
    minusNodes P a 3, minusNodes P a 4, h0Nodes P a 25, middleNodes P a 0,
    middleNodes P a 1, middleNodes P a 2, middleNodes P a 3, middleNodes P a 4,
    middleNodes P a 5, middleNodes P a 6, middleNodes P a 7, middleNodes P a 8,
    middleNodes P a 9, middleNodes P a 10, bottomNodes P a 10, minusSideNodes P a 2,
    bottomNodes P a 4, plusSideNodes P a 2, middleNodes P a 11, plusSideNodes P a 3,
    middleNodes P a 12, middleNodes P a 13, minusSideNodes P a 3, middleNodes P a 14]

/-- All twenty-five original top nodes and their reference transformations are retained. -/
theorem top_nodes (i : Fin 25) :
    nodes P a (topIndex i) = CoefficientPolynomialSpanUnitTop.nodes P a i := by
  fin_cases i <;> rfl

/-- The original fifteen-node bottom is identified nodewise, without asserting a monotone map. -/
theorem bottom_nodes (i : Fin 15) : nodes P a (bottomIndex i) = bottomNodes P a i := by
  fin_cases i
  · rfl
  · rfl
  · exact (terminal_nodes P a 0).symm
  · rfl
  · rfl
  · exact (terminal_nodes P a 1).symm
  · exact plus_bottom_first P a
  · exact plus_bottom_intermediate P a
  · exact (terminal_nodes P a 2).symm
  · rfl
  · rfl
  · exact (terminal_nodes P a 3).symm
  · exact minus_bottom_first P a
  · exact minus_bottom_intermediate P a
  · exact (terminal_nodes P a 4).symm

/-- The positive side retains its actual raw and normalized intermediate references. -/
theorem plus_side_nodes (i : Fin 8) :
    nodes P a (plusSideIndex i) = plusSideNodes P a i := by
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (plus_top_first P a).symm
  · exact (plus_top_intermediate P a).symm
  · exact ((plus_top_target P a).trans (plus_seven P a)).symm

/-- The inverse chart is kept separately through every original normalization step. -/
theorem minus_side_nodes (i : Fin 8) :
    nodes P a (minusSideIndex i) = minusSideNodes P a i := by
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (minus_top_first P a).symm
  · exact (minus_top_intermediate P a).symm
  · exact ((minus_top_target P a).trans (minus_seven P a)).symm

/-- All thirty-one H0 reference nodes are identified before any scalar parameter is evaluated. -/
theorem h0_nodes (i : Fin 31) : nodes P a (h0Index i) = h0Nodes P a i := by
  fin_cases i
  · rfl
  · rfl
  · exact (h0_plus_source P a 0).symm
  · exact (h0_plus_source P a 1).symm
  · rfl
  · exact (h0_plus_top P a 0).symm
  · exact (h0_plus_top P a 1).symm
  · exact (h0_plus_top P a 3).symm
  · rfl
  · exact (h0_plus_side P a 0).symm
  · exact (h0_plus_side P a 1).symm
  · exact (h0_plus_side P a 2).symm
  · exact (h0_plus_side P a 3).symm
  · exact (h0_plus_top P a 2).symm
  · exact (h0_minus_source P a 1).symm
  · rfl
  · exact (h0_minus_top P a 0).symm
  · exact (h0_minus_top P a 1).symm
  · exact (h0_minus_top P a 3).symm
  · rfl
  · exact (h0_minus_side P a 0).symm
  · exact (h0_minus_side P a 1).symm
  · exact (h0_minus_side P a 2).symm
  · exact (h0_minus_side P a 3).symm
  · exact (h0_minus_top P a 2).symm
  · rfl
  · exact (h0_plus_target P a 0).symm
  · exact (h0_plus_target P a 1).symm
  · exact (h0_plus_target P a 2).symm
  · exact (h0_minus_target P a 1).symm
  · exact (h0_minus_target P a 2).symm

/-- The genuine common-reference simplex determined by these actual original nodes. -/
def simplex : ModelSimplex (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
    (modelOf (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj a)))) 47 :=
  ModelSimplex.ofIsos (source P a) (fun i ↦ (nodes P a i).1) (fun i ↦ (nodes P a i).2)

/-- The entire top order is preserved; no such assertion is made for the other local diagrams. -/
def topFace : ⦋24⦌ ⟶ ⦋47⦌ :=
  SimplexCategory.Hom.mk ⟨topIndex, (by decide : StrictMono topIndex).monotone⟩

/-- The complete original top simplex occurs as a face with all of its actual arrows. -/
theorem top_face : (simplex P a).face topFace =
    CoefficientPolynomialSpanUnitTop.simplex P a := by
  unfold simplex CoefficientPolynomialSpanUnitTop.simplex
  rw [ModelSimplex.ofIsos_face]
  exact ModelSimplex.ofIsos_nodes_congr _ _ (top_nodes P a)

/-- An original triangle of a unit square, before its possibly nonmonotone enclosing relabeling. -/
def unitTriangleFace (i : Fin 6) : ⦋2⦌ ⟶ ⦋7⦌ :=
  SimplexCategory.Hom.mk ⟨unitTriangle i,
    (by decide : ∀ j : Fin 6, Monotone (unitTriangle j)) i⟩

/-- Each original positive-side triangle is monotone in the common support order. -/
def plusSideFace (i : Fin 6) : ⦋2⦌ ⟶ ⦋47⦌ :=
  BassH1Merged.supportedFace plusSideIndex (unitTriangleFace i)
    (plus_side_support i).monotone

/-- Each inverse-side triangle is transported with its own original chart labels. -/
def minusSideFace (i : Fin 6) : ⦋2⦌ ⟶ ⦋47⦌ :=
  BassH1Merged.supportedFace minusSideIndex (unitTriangleFace i)
    (minus_side_support i).monotone

/-- Each positive primitive face is the actual precomposed original unit-square face. -/
theorem plus_side_face (i : Fin 6) : (simplex P a).face (plusSideFace i) =
    ((OriginalUnitSquareSimplex.simplex (laurentPlus P a)).precomp
      (OriginalUnitSquareSimplex.sourceMap (polynomialProjection P a))).face
        (unitTriangleFace i) := by
  have h := BassH1Merged.supported_reference_face (source P a)
    (plusSideNodes P a) (nodes P a) plusSideIndex (plus_side_nodes P a)
    (unitTriangleFace i) (plus_side_support i).monotone
  rw [plus_side_family] at h
  exact h

/-- The inverse primitive faces retain the actual inverse Laurent chart and polynomial premap. -/
theorem minus_side_face (i : Fin 6) : (simplex P a).face (minusSideFace i) =
    ((OriginalUnitSquareSimplex.simplex (laurentMinus P a)).precomp
      (OriginalUnitSquareSimplex.sourceMap (polynomialProjection P a))).face
        (unitTriangleFace i) := by
  have h := BassH1Merged.supported_reference_face (source P a)
    (minusSideNodes P a) (nodes P a) minusSideIndex (minus_side_nodes P a)
    (unitTriangleFace i) (minus_side_support i).monotone
  rw [minus_side_family] at h
  exact h

/-- A four-node primitive face of the original bottom product grid. -/
def bottomGridSimplexFace (i : Fin 8) : ⦋3⦌ ⟶ ⦋14⦌ :=
  SimplexCategory.Hom.mk ⟨bottomGridFace i,
    (by decide : ∀ j : Fin 8, Monotone (bottomGridFace j)) i⟩

/-- Only the original four-node product support is embedded into the common order. -/
def bottomFace (i : Fin 8) : ⦋3⦌ ⟶ ⦋47⦌ :=
  BassH1Merged.supportedFace bottomIndex (bottomGridSimplexFace i)
    (bottom_grid_support i).monotone

/-- Each bottom primitive diagram is the original product of projection and Laurent identity. -/
theorem bottom_face (i : Fin 8) : (simplex P a).face (bottomFace i) =
    (CommonReferenceProduct.simplex (BassProjectionPath.source P a)
      (fun j ↦ (BassProjectionPath.nodes P a j).1)
      (fun j ↦ (BassProjectionPath.nodes P a j).2)
      (OriginalUnitSquareSimplex.unitSourceMap (space (op P, (laurentUnderFunctor R).obj a)))
      (CoefficientPolynomialSpanUnitSimplex.identityVertices
        (space (op P, (laurentUnderFunctor R).obj a)))
      (CoefficientPolynomialSpanUnitSimplex.identityReferences
        (space (op P, (laurentUnderFunctor R).obj a)))).face (bottomGridSimplexFace i) := by
  have h := BassH1Merged.supported_reference_face (source P a)
    (bottomNodes P a) (nodes P a) bottomIndex (bottom_nodes P a)
    (bottomGridSimplexFace i) (bottom_grid_support i).monotone
  rw [bottom_family] at h
  exact h

/-- One of the six unchanged eight-node split-triple supports in the original H0 diagram. -/
def h0TripleSimplexFace (i : Fin 6) : ⦋7⦌ ⟶ ⦋30⦌ :=
  SimplexCategory.Hom.mk ⟨h0TripleFace i,
    (by decide : ∀ j : Fin 6, Monotone (h0TripleFace j)) i⟩

/-- Each whole original split-triple face embeds without any further subdivision. -/
def h0Face (i : Fin 6) : ⦋7⦌ ⟶ ⦋47⦌ :=
  BassH1Merged.supportedFace h0Index (h0TripleSimplexFace i)
    (h0_triple_support i).monotone

/-- Every retained H0 face is the original coefficient-identity projection-pasting diagram. -/
theorem h0_face (i : Fin 6) : (simplex P a).face (h0Face i) =
    (BassH0Diagram.simplex P (𝟙 a)).face (h0TripleSimplexFace i) := by
  have h := BassH1Merged.supported_reference_face (source P a)
    (h0Nodes P a) (nodes P a) h0Index (h0_nodes P a)
    (h0TripleSimplexFace i) (h0_triple_support i).monotone
  rw [h0_family] at h
  exact h

end Quillen.PerfectComplexes.CoefficientBassUnitNodes
