/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1BottomCenter

/-! Full original projection rows on the external H1/bottom boundary. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.PolynomialBaseChange Quillen.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassH1Join
open BassH0Merge BassH1References
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

abbrev bottomJoinPost := BassH1Components.laurentMap P u ≫ BassH1Components.laurentMap P v

def firstSourceRowReference (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a) :=
  firstIso P u v ≪≫ isoWhiskerRight
    (eqToIso (BassH1H0Boundary.sourceAnchor P u α ha) ≪≫ BinaryNormalizationSimplex.total
      (coefficientMap P ((laurentUnderFunctor R).map u))
      (coefficientMap P (α.app a) ≫ polynomialProjection P a))
    (BassH1Components.laurentMap P v).functor

def bottomColumnReference := BassBottomCommonFamily.referenceIso P u v ≪≫
  isoWhiskerLeft (BassProjectionPath.source P a).functor
    (BinaryNormalizationSimplex.total
      (coefficientMap P ((laurentUnderFunctor R).map v))
      (coefficientMap P ((laurentUnderFunctor R).map u)))

/-- The original positive projection row after both actual Laurent coefficient maps. -/
theorem first_source_plus_row (i : Fin 3) :
    BassH1References.firstNodes P u v
      (BassH0Diagram.plusFace.toOrderHom (rectangleLeftIndex i)) =
    postReferenceNode (BassOverlap.commonReference P u v) (bottomJoinPost P u v)
      (H := BinaryNormalizationSimplex.sourceMap (laurentPlus P a) (polynomialProjection P a))
      (firstSourceRowReference P u v (underToLaurent R) (laurentPlus_projection P a))
      (binaryNodes (laurentPlus P a) (polynomialProjection P a) i) := by
  have hn := congrArg (postReferenceNode (BassOverlap.commonReference P u v)
    (BassH1Components.laurentMap P v) (firstIso P u v)) (BassH1H0Boundary.plus_source P u i)
  exact hn.trans (post_post_node (BassOverlap.commonReference P u v)
    (BassH1Components.laurentMap P u) (BassH1Components.laurentMap P v)
    (BinaryNormalizationSimplex.sourceMap (laurentPlus P a) (polynomialProjection P a))
    _ (firstIso P u v) _)

/-- The original inverse projection row retains its separate projection source equality. -/
theorem first_source_minus_row (i : Fin 3) :
    BassH1References.firstNodes P u v
      (BassH0Diagram.minusFace.toOrderHom (rectangleLeftIndex i)) =
    postReferenceNode (BassOverlap.commonReference P u v) (bottomJoinPost P u v)
      (H := BinaryNormalizationSimplex.sourceMap (laurentMinus P a) (polynomialProjection P a))
      (firstSourceRowReference P u v (underToLaurentInvert R) (laurentMinus_projection P a))
      (binaryNodes (laurentMinus P a) (polynomialProjection P a) i) := by
  have hn := congrArg (postReferenceNode (BassOverlap.commonReference P u v)
    (BassH1Components.laurentMap P v) (firstIso P u v)) (BassH1H0Boundary.minus_source P u i)
  exact hn.trans (post_post_node (BassOverlap.commonReference P u v)
    (BassH1Components.laurentMap P u) (BassH1Components.laurentMap P v)
    (BinaryNormalizationSimplex.sourceMap (laurentMinus P a) (polynomialProjection P a))
    _ (firstIso P u v) _)

/-- The bottom target column is the original Bass projection family after both Laurent maps. -/
theorem bottom_target_column (i : Fin 5) :
    BassBottomCommonFamily.bottomNodes P u v (Quillen.SimplexGrid.index 4 2 (i, 2)) =
      postReferenceNode (BassOverlap.commonReference P u v) (bottomJoinPost P u v)
        (bottomColumnReference P u v) (BassProjectionPath.nodes P a i) :=
  product_column_nodes (BassOverlap.commonReference P u v)
    (BassProjectionPath.source P a) (fun i ↦ (BassProjectionPath.nodes P a i).1)
    (fun i ↦ (BassProjectionPath.nodes P a i).2)
    (BassLaurentBottomFace.source P u v) (BassLaurentBottomFace.vertices P u v)
    (BassLaurentBottomFace.references P u v) (BassBottomCommonFamily.referenceIso P u v) i 2

/-- The positive bottom row retains the original two binary normalization transformations. -/
theorem bottom_target_plus_row (i : Fin 3) :
    BassBottomCommonFamily.bottomNodes P u v
      (Quillen.SimplexGrid.index 4 2 (BassProjectionPath.plusFace.toOrderHom i, 2)) =
    postReferenceNode (BassOverlap.commonReference P u v) (bottomJoinPost P u v)
      (bottomColumnReference P u v)
      (binaryNodes (laurentPlus P a) (polynomialProjection P a) i) :=
  (bottom_target_column P u v _).trans (post_square_first_nodes
    (laurentPlus P a) (polynomialProjection P a) (laurentMinus P a) (polynomialProjection P a)
    ((laurentPlus_projection P a).trans (laurentMinus_projection P a).symm)
    (BassOverlap.commonReference P u v) (bottomJoinPost P u v) (bottomColumnReference P u v) i)

/-- The inverse bottom row includes the unchanged positive-to-inverse source equality. -/
theorem bottom_target_minus_row (i : Fin 3) :
    BassBottomCommonFamily.bottomNodes P u v
      (Quillen.SimplexGrid.index 4 2 (BassProjectionPath.minusFace.toOrderHom i, 2)) =
    postReferenceNode (BassOverlap.commonReference P u v) (bottomJoinPost P u v)
      (bottomColumnReference P u v ≪≫
        isoWhiskerRight (BassProjectionPath.sourceIso P a) (bottomJoinPost P u v).functor)
      (binaryNodes (laurentMinus P a) (polynomialProjection P a) i) :=
  (bottom_target_column P u v _).trans (post_square_second_nodes
    (laurentPlus P a) (polynomialProjection P a) (laurentMinus P a) (polynomialProjection P a)
    ((laurentPlus_projection P a).trans (laurentMinus_projection P a).symm)
    (BassOverlap.commonReference P u v) (bottomJoinPost P u v) (bottomColumnReference P u v) i)

/-- Full positive source row shared by the original first H1 cell and original bottom face. -/
theorem first_bottom_plus_nodes (i : Fin 3) :
    BassH1References.firstNodes P u v
      (BassH0Diagram.plusFace.toOrderHom (rectangleLeftIndex i)) =
    BassBottomCommonFamily.bottomNodes P u v
      (Quillen.SimplexGrid.index 4 2 (BassProjectionPath.plusFace.toOrderHom i, 2)) :=
  post_families_match (BassOverlap.commonReference P u v) (bottomJoinPost P u v)
    (BinaryNormalizationSimplex.sourceMap (laurentPlus P a) (polynomialProjection P a))
    (binaryNodes (laurentPlus P a) (polynomialProjection P a))
    (first_source_plus_row P u v) (bottom_target_plus_row P u v) 0 (first_bottom_center P u v) i

/-- The full inverse row uses the same proved central node and its actual native transports. -/
theorem first_bottom_minus_nodes (i : Fin 3) :
    BassH1References.firstNodes P u v
      (BassH0Diagram.minusFace.toOrderHom (rectangleLeftIndex i)) =
    BassBottomCommonFamily.bottomNodes P u v
      (Quillen.SimplexGrid.index 4 2 (BassProjectionPath.minusFace.toOrderHom i, 2)) :=
  post_families_match (BassOverlap.commonReference P u v) (bottomJoinPost P u v)
    (BinaryNormalizationSimplex.sourceMap (laurentMinus P a) (polynomialProjection P a))
    (binaryNodes (laurentMinus P a) (polynomialProjection P a))
    (first_source_minus_row P u v) (bottom_target_minus_row P u v) 0 (first_bottom_center P u v) i

/-- Every dependent node on the entire external source edge is shared with the original bottom. -/
theorem first_bottom_nodes (i : Fin 5) :
    BassH1References.firstNodes P u v (middleSourceFace.toOrderHom i) =
    BassBottomCommonFamily.bottomNodes P u v (Quillen.SimplexGrid.index 4 2 (i, 2)) := by
  fin_cases i
  · exact first_bottom_center P u v
  · exact first_bottom_plus_nodes P u v 1
  · exact first_bottom_plus_nodes P u v 2
  · exact first_bottom_minus_nodes P u v 1
  · exact first_bottom_minus_nodes P u v 2

/-- The entire source edge agrees with the fixed old44 boundary nodes. -/
theorem first_old_bottom_nodes (i : Fin 5) :
    BassH1References.firstNodes P u v (middleSourceFace.toOrderHom i) =
    BassReferenceMerge.nodes P u v
      (BassReferenceMerge.bottomFace.toOrderHom (Quillen.SimplexGrid.index 4 2 (i, 2))) := by
  have hb := BassReferenceMerge.bottom_nodes P u v (Quillen.SimplexGrid.index 4 2 (i, 2))
  change BassReferenceMerge.nodes P u v
    (BassReferenceMerge.bottomFace.toOrderHom (Quillen.SimplexGrid.index 4 2 (i, 2))) =
    BassBottomCommonFamily.nodes P u v (Fin.natAdd 36 (Quillen.SimplexGrid.index 4 2 (i, 2))) at hb
  unfold BassBottomCommonFamily.nodes at hb
  rw [Fin.addCases_right] at hb
  exact (first_bottom_nodes P u v i).trans hb.symm

/-- All five complete source-edge nodes lie in the fixed actual old62 family. -/
theorem first_old62_bottom_nodes (i : Fin 5) :
    BassH1References.firstNodes P u v (middleSourceFace.toOrderHom i) =
    BassH0Merged.nodes P u v (BassSupportOrder.oldIndex
      (BassReferenceMerge.bottomFace.toOrderHom (Quillen.SimplexGrid.index 4 2 (i, 2)))) :=
  (first_old_bottom_nodes P u v i).trans (BassH0Merged.old_nodes P u v _).symm

end Quillen.PerfectComplexes.BassH1Join
