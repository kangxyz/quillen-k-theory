/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputCompositionTerminalProducts
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ProjectionRectangleSquareRows
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ProjectionFirstNormalNode

/-!
# Complete original product-to-middle terminal row nodes

Both actual five-node product rows agree with the unchanged original input chart rows after
base precomposition. The proof retains the full dependent reference, using only actual
projection naturality and normalized three-factor composition coherence.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.PerfectComplexes.BassReferenceMerge
open Quillen.PerfectComplexes.BassH0Merge Quillen.PerfectComplexes.BassH1Join
universe u
namespace Quillen.PerfectComplexes.GlobalRawBass.InputCompositionTerminalRows
open InputCompositionTerminalAttach InputCompositionTerminalProducts
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable (k : laurent ⟶ polynomial)
  (hk : ∀ V, k.app V ≫ projection.app V = laurentProjection.app V)

/-- The actual chart row in the original first-arrow input surface. -/
abbrev chartAnchor := ProjectionRectangleSquareRows.chartAnchor
  (projection.app Y) (k.app Y) (laurent.map f) (laurentProjection.app Y) (hk Y)

/-- The original source equality of that chart row, retaining its right association. -/
abbrev chartGeom := projection_first_geom (projection.app Y) (k.app Y)
  (laurent.map f) (laurentProjection.app Y) (hk Y)

/-- The entire chart anchor has its original two-factor normalized form. -/
theorem chart_anchor_normal : chartAnchor f k hk =
    smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (chartGeom f k hk)) ≪≫
      boundedFlatNormalizedPullbackCompIso (laurent.map f ≫ k.app Y) (projection.app Y)) := by
  have h := projection_first_normal_reference
    (projection.app Y) (k.app Y) (projection.app X) (k.app X)
    f (polynomial.map f) (laurent.map f) (projection.naturality f) (k.naturality f)
    (laurentProjection.app Y) (hk Y)
  change chartAnchor f k hk = _ at h
  refine h.trans ?_
  rw [smallIso_trans, smallIso_eqToIso]
  rfl

/-- Both rows use the same literal composite model premap. -/
abbrev rowPremap := arrow g ≫ arrow (projection.app Y)

/-- The full middle-row reference includes both original precomposition anchors. -/
def middleAnchor := preAnchor f g ≪≫ isoWhiskerLeft (arrow g).functor (chartAnchor f k hk)

/-- The product row keeps the final polynomial-square reference before its chart factor. -/
def productAnchor := sourceIso f g k hk ≪≫
  isoWhiskerRight (polynomialNodes g 4).2 (chartSource f k).functor

/-- The two complete row anchors agree by the actual original three-factor coherence. -/
theorem row_reference : middleAnchor f g k hk = productAnchor f g k hk := by
  have hp : (polynomialNodes g 4).2 =
      smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (projection.naturality g)) ≪≫
        boundedFlatNormalizedPullbackCompIso (projection.app Y) g) := by
    rw [smallIso_trans, smallIso_eqToIso]
    rfl
  change preAnchor f g ≪≫ isoWhiskerLeft (arrow g).functor (chartAnchor f k hk) =
    sourceIso f g k hk ≪≫ isoWhiskerRight (polynomialNodes g 4).2 (chartSource f k).functor
  rw [chart_anchor_normal, hp]
  change smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (pre_total f g).symm) ≪≫
      boundedFlatNormalizedPullbackCompIso (laurent.map f ≫ laurentProjection.app Y) g) ≪≫
    isoWhiskerLeft (AsSmall.down ⋙ boundedFlatNormalizedPullback g ⋙ AsSmall.up)
      (smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (chartGeom f k hk)) ≪≫
        boundedFlatNormalizedPullbackCompIso (laurent.map f ≫ k.app Y) (projection.app Y))) =
    smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (total f g k hk).symm) ≪≫
      boundedFlatNormalizedPullbackCompIso (laurent.map f ≫ k.app Y)
        (polynomial.map g ≫ projection.app Z)) ≪≫
    isoWhiskerRight
      (smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (projection.naturality g)) ≪≫
        boundedFlatNormalizedPullbackCompIso (projection.app Y) g))
      (AsSmall.down ⋙ boundedFlatNormalizedPullback (laurent.map f ≫ k.app Y) ⋙ AsSmall.up)
  rw [smallIso_precomp, smallIso_postcomp, ← smallIso_trans, ← smallIso_trans]
  apply congrArg smallIso
  simpa only [Iso.trans_assoc] using
    (anchored_factorizations_strict (laurent.map f ≫ k.app Y) (projection.app Y) g
      (laurent.map f ≫ laurentProjection.app Y) (polynomial.map g ≫ projection.app Z)
      (laurent.map (f ≫ g) ≫ laurentProjection.app Z)
      (chartGeom f k hk) (projection.naturality g) (pre_total f g).symm
      (total f g k hk).symm)

/-- All five original middle-row nodes keep their two complete precomposition references. -/
theorem middle_row (i : Fin 5) :
    preNode f g (InputDescSimplex.chartNodes f k hk
      (ProjectionRectangleSquareRows.chartRow i)) =
    preReferenceNode (InputCompositionCarrierCharts.source f g) (rowPremap g)
      (H := chartSource f k) (middleAnchor f g k hk) (chartNodes f k i) := by
  have h := congrArg (preNode f g)
    (ProjectionRectangleSquareRows.chart_row_nodes
      (projection.app Y) (k.app Y) (projection.app X) (k.app X)
      f (polynomial.map f) (laurent.map f) (projection.naturality f) (k.naturality f)
      (laurentProjection.app Y) (hk Y) i)
  exact h.trans (pre_pre_node (InputCompositionCarrierCharts.source f g)
    (arrow g) (arrow (projection.app Y)) (chartSource f k)
    (chartAnchor f k hk) (preAnchor f g) (chartNodes f k i))

/-- The actual last product row retains the whole original chart-node family. -/
theorem product_row (i : Fin 5) :
    nodes f g k hk (Quillen.SimplexGrid.index 4 4 (4, i)) =
    preReferenceNode (InputCompositionCarrierCharts.source f g) (rowPremap g)
      (H := chartSource f k) (productAnchor f g k hk) (chartNodes f k i) :=
  product_row_nodes (InputCompositionCarrierCharts.source f g) (polynomialSource g)
    (fun j ↦ (polynomialNodes g j).1) (fun j ↦ (polynomialNodes g j).2)
    (chartSource f k) (fun j ↦ (chartNodes f k j).1) (fun j ↦ (chartNodes f k j).2)
    (sourceIso f g k hk) 4 i

/-- Every full dependent node on either actual product/middle join is equal before evaluation. -/
theorem row_nodes (i : Fin 5) :
    preNode f g (InputDescSimplex.chartNodes f k hk
      (ProjectionRectangleSquareRows.chartRow i)) =
      nodes f g k hk (Quillen.SimplexGrid.index 4 4 (4, i)) := by
  rw [middle_row, row_reference]
  exact (product_row f g k hk i).symm

end Quillen.PerfectComplexes.GlobalRawBass.InputCompositionTerminalRows
