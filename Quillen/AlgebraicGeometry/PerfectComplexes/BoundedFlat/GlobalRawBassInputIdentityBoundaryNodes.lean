/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputIdentityUnitBoundaryNodes

/-!
# Actual initial-surface boundary nodes for the global raw identity carrier

The full global thirty-one-node input surface is attached to the actual unit-side, polynomial-top,
projection-by-Laurent-unit, and base-unit-by-projection node families. Every equality retains
both the model morphism and its complete reference transformation.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace Quillen.PerfectComplexes.GlobalRawBass.InputIdentityBoundaryNodes
open OriginalUnitSquareSimplex CoefficientBassUnitHZeroNodes BassH0Merge BassH1Join
open InputIdentityTopNodes InputIdentityUnitBoundaryNodes

private theorem post_identity_anchor {V W T : Model.{u}} (F : V ⟶ T)
    (H : V ⟶ W) (J : W ⟶ T) (ρ : F.functor ≅ (H ≫ J).functor)
    (N : Σ G : V ⟶ W, H.functor ≅ G.functor) :
    postReferenceNode F J (ρ ≪≫ isoWhiskerLeft H.functor (Iso.refl J.functor)) N =
      postReferenceNode F J ρ N := by
  rw [isoWhiskerLeft_refl]
  exact congrArg (fun σ ↦ postReferenceNode F J σ N) (Iso.trans_refl ρ)

private theorem pre_identity_anchor {V W T : Model.{u}} (F : V ⟶ T)
    (J : V ⟶ W) (H : W ⟶ T) (ρ : F.functor ≅ (J ≫ H).functor)
    (N : Σ G : W ⟶ T, H.functor ≅ G.functor) :
    preReferenceNode F J (ρ ≪≫ isoWhiskerRight (Iso.refl J.functor) H.functor) N =
      preReferenceNode F J ρ N := by
  rw [isoWhiskerRight_refl]
  exact congrArg (fun σ ↦ preReferenceNode F J σ N) (Iso.trans_refl ρ)

variable (X : Scheme.{u})

/-- Both original lower positive chart rows retain all their actual reference nodes. -/
theorem plus_side_right (i : Fin 3) :
    InputIdentityNodes.chartNodes X plus plus_projection
      (DoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i)) =
      plusSideNodes X (![0, 1, 2] i) := by
  exact (InputIdentityNodes.chart_identity X plus plus_projection _).trans
    ((rectangle_side_right _ _ _ _ i).trans
    (congrArg (fun ρ ↦ preReferenceNode (source X) (sourceMap (projection.app X))
      ρ ⟨vertices (plus.app X) (![0, 1, 2] i), references (plus.app X) (![0, 1, 2] i)⟩)
      (plus_total_anchor X)))

theorem plus_side_left (i : Fin 3) :
    InputIdentityNodes.chartNodes X plus plus_projection
      (DoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i)) =
      plusSideNodes X (![0, 4, 5] i) := by
  exact (InputIdentityNodes.chart_identity X plus plus_projection _).trans
    ((rectangle_side_left _ _ _ _ i).trans
    (congrArg (fun ρ ↦ preReferenceNode (source X) (sourceMap (projection.app X))
      ρ ⟨vertices (plus.app X) (![0, 4, 5] i), references (plus.app X) (![0, 4, 5] i)⟩)
      (plus_total_anchor X)))

/-- The inverse chart retains its own two original binary rows and their full references. -/
theorem minus_side_right (i : Fin 3) :
    InputIdentityNodes.chartNodes X minus minus_projection
      (DoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i)) =
      minusSideNodes X (![0, 1, 2] i) := by
  exact (InputIdentityNodes.chart_identity X minus minus_projection _).trans
    ((rectangle_side_right _ _ _ _ i).trans
    (congrArg (fun ρ ↦ preReferenceNode (source X) (sourceMap (projection.app X))
      ρ ⟨vertices (minus.app X) (![0, 1, 2] i), references (minus.app X) (![0, 1, 2] i)⟩)
      (minus_total_anchor X)))

theorem minus_side_left (i : Fin 3) :
    InputIdentityNodes.chartNodes X minus minus_projection
      (DoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i)) =
      minusSideNodes X (![0, 4, 5] i) := by
  exact (InputIdentityNodes.chart_identity X minus minus_projection _).trans
    ((rectangle_side_left _ _ _ _ i).trans
    (congrArg (fun ρ ↦ preReferenceNode (source X) (sourceMap (projection.app X))
      ρ ⟨vertices (minus.app X) (![0, 4, 5] i), references (minus.app X) (![0, 4, 5] i)⟩)
      (minus_total_anchor X)))

/-- The positive polynomial columns use the exact original top-square nodes. -/
theorem plus_top_right (i : Fin 3) :
    InputIdentityNodes.chartNodes X plus plus_projection
      (DoubleSquareMergedSimplex.middleFace.toOrderHom (leftIndex i)) =
      plusNodes X (![0, 1, 2] i) := by
  exact (InputIdentityNodes.chart_identity X plus plus_projection _).trans
    ((rectangle_top_right _ _ _ _ i).trans
    (congrArg (fun ρ ↦ postReferenceNode (source X) (sourceMap (plus.app X))
      ρ ⟨vertices (projection.app X) (![0, 1, 2] i),
        references (projection.app X) (![0, 1, 2] i)⟩) (plus_total_anchor X)))

theorem plus_top_left (i : Fin 3) :
    InputIdentityNodes.chartNodes X plus plus_projection
      (DoubleSquareMergedSimplex.lastFace.toOrderHom (leftIndex i)) =
      plusNodes X (![0, 4, 5] i) := by
  exact (InputIdentityNodes.chart_identity X plus plus_projection _).trans
    ((rectangle_top_left _ _ _ _ i).trans
    (congrArg (fun ρ ↦ postReferenceNode (source X) (sourceMap (plus.app X))
      ρ ⟨vertices (projection.app X) (![0, 4, 5] i),
        references (projection.app X) (![0, 4, 5] i)⟩) (plus_total_anchor X)))

/-- The inverse polynomial columns keep their distinct original top-square references. -/
theorem minus_top_right (i : Fin 3) :
    InputIdentityNodes.chartNodes X minus minus_projection
      (DoubleSquareMergedSimplex.middleFace.toOrderHom (leftIndex i)) =
      minusNodes X (![0, 1, 2] i) := by
  exact (InputIdentityNodes.chart_identity X minus minus_projection _).trans
    ((rectangle_top_right _ _ _ _ i).trans
    (congrArg (fun ρ ↦ postReferenceNode (source X) (sourceMap (minus.app X))
      ρ ⟨vertices (projection.app X) (![0, 1, 2] i),
        references (projection.app X) (![0, 1, 2] i)⟩) (minus_total_anchor X)))

theorem minus_top_left (i : Fin 3) :
    InputIdentityNodes.chartNodes X minus minus_projection
      (DoubleSquareMergedSimplex.lastFace.toOrderHom (leftIndex i)) =
      minusNodes X (![0, 4, 5] i) := by
  exact (InputIdentityNodes.chart_identity X minus minus_projection _).trans
    ((rectangle_top_left _ _ _ _ i).trans
    (congrArg (fun ρ ↦ postReferenceNode (source X) (sourceMap (minus.app X))
      ρ ⟨vertices (projection.app X) (![0, 4, 5] i),
        references (projection.app X) (![0, 4, 5] i)⟩) (minus_total_anchor X)))

/-- The positive projection row consists of the three unchanged original binary nodes. -/
theorem projection_plus_row (i : Fin 3) :
    InputIdentityProjection.nodes X (![0, 1, 2] i) =
      binaryNodes (plus.app X) (projection.app X) i := by
  fin_cases i <;> rfl

/-- The inverse row retains its original source transport before either normalization step. -/
theorem projection_minus_row (i : Fin 3) :
    InputIdentityProjection.nodes X (![0, 3, 4] i) =
      anchorNode (InputIdentityProjection.sourceIso X)
        (binaryNodes (minus.app X) (projection.app X) i) := by
  fin_cases i
  · apply ModelSimplex.reference_node_eq (InputIdentityProjection.source_eq X)
    simp [InputIdentityProjection.sourceIso, binaryNodes]
  · rfl
  · rfl

/-- The actual initial bottom column is the original Bass nodes under fixed Laurent identity. -/
theorem bottom_initial_column (j : Fin 5) :
    bottomNodes X (Quillen.SimplexGrid.index 4 2 (j, 0)) =
      postReferenceNode (source X)
        (unitSourceMap (laurent.obj X)) (bottomSourceIso X)
        (InputIdentityProjection.nodes X j) := by
  have h := product_column_nodes (source X) (InputIdentityProjection.source X)
    (fun i ↦ (InputIdentityProjection.nodes X i).1) (fun i ↦ (InputIdentityProjection.nodes X i).2)
    (unitSourceMap (laurent.obj X))
    (CoefficientPolynomialSpanUnitSimplex.identityVertices
      (laurent.obj X))
    (CoefficientPolynomialSpanUnitSimplex.identityReferences
      (laurent.obj X)) (bottomSourceIso X) j 0
  change bottomNodes X (Quillen.SimplexGrid.index 4 2 (j, 0)) =
    postReferenceNode (source X)
      (unitSourceMap (laurent.obj X))
      (bottomSourceIso X ≪≫ isoWhiskerLeft (InputIdentityProjection.source X).functor
        (Iso.refl _)) (InputIdentityProjection.nodes X j) at h
  exact h.trans (post_identity_anchor (source X) (InputIdentityProjection.source X)
    (unitSourceMap (laurent.obj X)) (bottomSourceIso X)
    (InputIdentityProjection.nodes X j))

/-- The actual first top row is the same Bass node family under fixed original base identity. -/
theorem top_initial_row (j : Fin 5) :
    middleNodes X (Quillen.SimplexGrid.index 2 4 (0, j)) =
      preReferenceNode (source X) (unitSourceMap X) (Iso.refl _)
        (InputIdentityProjection.nodes X j) := by
  have h := product_row_nodes (source X) (unitSourceMap X)
    (CoefficientPolynomialSpanUnitSimplex.identityVertices X)
    (CoefficientPolynomialSpanUnitSimplex.identityReferences X)
    (InputIdentityProjection.source X) (fun i ↦ (InputIdentityProjection.nodes X i).1)
    (fun i ↦ (InputIdentityProjection.nodes X i).2) (Iso.refl _) 0 j
  change middleNodes X (Quillen.SimplexGrid.index 2 4 (0, j)) =
    preReferenceNode (source X) (unitSourceMap X)
      (Iso.refl _ ≪≫ isoWhiskerRight (Iso.refl _) (InputIdentityProjection.source X).functor)
      (InputIdentityProjection.nodes X j) at h
  exact h.trans (pre_identity_anchor (source X) (unitSourceMap X)
    (InputIdentityProjection.source X) (Iso.refl _) (InputIdentityProjection.nodes X j))

theorem bottom_plus_form (i : Fin 3) :
    bottomNodes X (Quillen.SimplexGrid.index 4 2 (![0, 1, 2] i, 0)) =
      postReferenceNode (source X)
        (unitSourceMap (laurent.obj X)) (bottomSourceIso X)
        (binaryNodes (plus.app X) (projection.app X) i) := by
  rw [bottom_initial_column, projection_plus_row]

theorem bottom_minus_form (i : Fin 3) :
    bottomNodes X (Quillen.SimplexGrid.index 4 2 (![0, 3, 4] i, 0)) =
      postReferenceNode (source X)
        (unitSourceMap (laurent.obj X))
        (bottomSourceIso X ≪≫ isoWhiskerRight (InputIdentityProjection.sourceIso X)
          (unitSourceMap (laurent.obj X)).functor)
        (binaryNodes (minus.app X) (projection.app X) i) := by
  rw [bottom_initial_column, projection_minus_row]
  exact post_anchor_node _ _ _ _ _

theorem top_plus_form (i : Fin 3) :
    middleNodes X (Quillen.SimplexGrid.index 2 4 (0, ![0, 1, 2] i)) =
      preReferenceNode (source X) (unitSourceMap X) (Iso.refl _)
        (binaryNodes (plus.app X) (projection.app X) i) := by
  rw [top_initial_row, projection_plus_row]

theorem top_minus_form (i : Fin 3) :
    middleNodes X (Quillen.SimplexGrid.index 2 4 (0, ![0, 3, 4] i)) =
      preReferenceNode (source X) (unitSourceMap X)
        (isoWhiskerLeft (unitSourceMap X).functor
          (InputIdentityProjection.sourceIso X))
        (binaryNodes (minus.app X) (projection.app X) i) := by
  rw [top_initial_row, projection_minus_row, pre_anchor_node]
  simp only [Iso.refl_trans]

/-- Every positive source-projection node is its unchanged bottom-column node. -/
theorem plus_source_projection (i : Fin 3) :
    InputIdentityNodes.chartNodes X plus plus_projection
      (DoubleSquareMergedSimplex.firstFace.toOrderHom (leftIndex i)) =
      bottomNodes X (Quillen.SimplexGrid.index 4 2 (![0, 1, 2] i, 0)) := by
  apply post_families_match (source X)
    (unitSourceMap (laurent.obj X))
    (BinaryNormalizationSimplex.sourceMap (plus.app X) (projection.app X))
    (binaryNodes (plus.app X) (projection.app X))
    (fun j ↦ (InputIdentityNodes.chart_identity X plus plus_projection _).trans
      (rectangle_source_column_form _ _ _ _ j)) (bottom_plus_form X) 2 ?_ i
  exact (plus_side_right X 2).trans (plus_bottom_first X)

/-- Every inverse source-projection node retains its separate original chart reference. -/
theorem minus_source_projection (i : Fin 3) :
    InputIdentityNodes.chartNodes X minus minus_projection
      (DoubleSquareMergedSimplex.firstFace.toOrderHom (leftIndex i)) =
      bottomNodes X (Quillen.SimplexGrid.index 4 2 (![0, 3, 4] i, 0)) := by
  apply post_families_match (source X)
    (unitSourceMap (laurent.obj X))
    (BinaryNormalizationSimplex.sourceMap (minus.app X) (projection.app X))
    (binaryNodes (minus.app X) (projection.app X))
    (fun j ↦ (InputIdentityNodes.chart_identity X minus minus_projection _).trans
      (rectangle_source_column_form _ _ _ _ j)) (bottom_minus_form X) 2 ?_ i
  exact (minus_side_right X 2).trans (minus_bottom_first X)

/-- Every positive target-projection node is the unchanged initial top-grid row. -/
theorem plus_target_projection (i : Fin 3) :
    InputIdentityNodes.chartNodes X plus plus_projection
      (DoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i)) =
      middleNodes X (Quillen.SimplexGrid.index 2 4 (0, ![0, 1, 2] i)) := by
  apply pre_families_match (source X) (unitSourceMap X)
    (BinaryNormalizationSimplex.sourceMap (plus.app X) (projection.app X))
    (binaryNodes (plus.app X) (projection.app X))
    (fun j ↦ (InputIdentityNodes.chart_identity X plus plus_projection _).trans
      (rectangle_target_row_form _ _ _ _ j)) (top_plus_form X) 2 ?_ i
  exact (plus_top_left X 2).trans (plus_shared X 0)

/-- The inverse target row retains both original raw and normalized comparison vertices. -/
theorem minus_target_projection (i : Fin 3) :
    InputIdentityNodes.chartNodes X minus minus_projection
      (DoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i)) =
      middleNodes X (Quillen.SimplexGrid.index 2 4 (0, ![0, 3, 4] i)) := by
  apply pre_families_match (source X) (unitSourceMap X)
    (BinaryNormalizationSimplex.sourceMap (minus.app X) (projection.app X))
    (binaryNodes (minus.app X) (projection.app X))
    (fun j ↦ (InputIdentityNodes.chart_identity X minus minus_projection _).trans
      (rectangle_target_row_form _ _ _ _ j)) (top_minus_form X) 2 ?_ i
  exact (minus_top_left X 2).trans (minus_shared X 0)

/-- The five actual plus side boundary nodes, in their original path order. -/
theorem h0_plus_side (i : Fin 5) :
    InputIdentityNodes.nodes X (BassH0Diagram.plusFace.toOrderHom (![9, 10, 11, 12, 13] i)) =
      plusSideNodes X (![0, 1, 2, 4, 5] i) := by
  rw [InputIdentityNodes.plus_nodes]
  fin_cases i
  · exact plus_side_right X 0
  · exact plus_side_right X 1
  · exact plus_side_right X 2
  · exact plus_side_left X 1
  · exact plus_side_left X 2

/-- The five actual plus top boundary nodes, in their original path order. -/
theorem h0_plus_top (i : Fin 5) :
    InputIdentityNodes.nodes X (BassH0Diagram.plusFace.toOrderHom (![5, 6, 13, 7, 17] i)) =
      plusNodes X (![0, 1, 2, 4, 5] i) := by
  rw [InputIdentityNodes.plus_nodes]
  fin_cases i
  · exact plus_top_right X 0
  · exact plus_top_right X 1
  · exact plus_top_right X 2
  · exact plus_top_left X 1
  · exact plus_top_left X 2

/-- The three actual plus source projection nodes retain both binary normalization steps. -/
theorem h0_plus_source (i : Fin 3) :
    InputIdentityNodes.nodes X (BassH0Diagram.plusFace.toOrderHom (![2, 3, 11] i)) =
      bottomNodes X (![0, 3, 6] i) := by
  rw [InputIdentityNodes.plus_nodes]
  fin_cases i
  · exact plus_source_projection X 0
  · exact plus_source_projection X 1
  · exact plus_source_projection X 2

/-- The three actual plus target projection nodes retain both binary normalization steps. -/
theorem h0_plus_target (i : Fin 3) :
    InputIdentityNodes.nodes X (BassH0Diagram.plusFace.toOrderHom (![15, 16, 17] i)) =
      middleNodes X (![0, 1, 2] i) := by
  rw [InputIdentityNodes.plus_nodes]
  fin_cases i
  · exact plus_target_projection X 0
  · exact plus_target_projection X 1
  · exact plus_target_projection X 2

/-- The five actual minus side boundary nodes, in their original path order. -/
theorem h0_minus_side (i : Fin 5) :
    InputIdentityNodes.nodes X (BassH0Diagram.minusFace.toOrderHom (![9, 10, 11, 12, 13] i)) =
      minusSideNodes X (![0, 1, 2, 4, 5] i) := by
  rw [InputIdentityNodes.minus_nodes]
  fin_cases i
  · exact minus_side_right X 0
  · exact minus_side_right X 1
  · exact minus_side_right X 2
  · exact minus_side_left X 1
  · exact minus_side_left X 2

/-- The five actual minus top boundary nodes, in their original path order. -/
theorem h0_minus_top (i : Fin 5) :
    InputIdentityNodes.nodes X (BassH0Diagram.minusFace.toOrderHom (![5, 6, 13, 7, 17] i)) =
      minusNodes X (![0, 1, 2, 4, 5] i) := by
  rw [InputIdentityNodes.minus_nodes]
  fin_cases i
  · exact minus_top_right X 0
  · exact minus_top_right X 1
  · exact minus_top_right X 2
  · exact minus_top_left X 1
  · exact minus_top_left X 2

/-- The three actual minus source projection nodes retain both binary normalization steps. -/
theorem h0_minus_source (i : Fin 3) :
    InputIdentityNodes.nodes X (BassH0Diagram.minusFace.toOrderHom (![2, 3, 11] i)) =
      bottomNodes X (![0, 9, 12] i) := by
  rw [InputIdentityNodes.minus_nodes]
  fin_cases i
  · exact minus_source_projection X 0
  · exact minus_source_projection X 1
  · exact minus_source_projection X 2

/-- The three actual minus target projection nodes retain both binary normalization steps. -/
theorem h0_minus_target (i : Fin 3) :
    InputIdentityNodes.nodes X (BassH0Diagram.minusFace.toOrderHom (![15, 16, 17] i)) =
      middleNodes X (![0, 3, 4] i) := by
  rw [InputIdentityNodes.minus_nodes]
  fin_cases i
  · exact minus_target_projection X 0
  · exact minus_target_projection X 1
  · exact minus_target_projection X 2


end Quillen.PerfectComplexes.GlobalRawBass.InputIdentityBoundaryNodes
