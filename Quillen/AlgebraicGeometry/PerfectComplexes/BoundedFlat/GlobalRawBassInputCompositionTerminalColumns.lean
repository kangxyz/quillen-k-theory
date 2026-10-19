/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputCompositionTerminalProducts
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ProjectionRectangleSquareRows
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ProjectionMiddleNormalNode

/-!
# Complete original first-to-product terminal column nodes

All five original polynomial-square nodes survive actual Laurent postcomposition and agree
with their complete product-column references. The two charts retain their distinct original
projection transports and naturality equalities throughout.
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
namespace Quillen.PerfectComplexes.GlobalRawBass.InputCompositionTerminalColumns
open InputCompositionTerminalAttach InputCompositionTerminalProducts

universe v

-- Factor the complete source transport before specializing any geometric model arrows.
private theorem smallIso_transport_trans
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    {F₀ F₁ F₂ F₃ : C ⥤ D}
    (h₀₁ : F₀ = F₁) (h₁₂ : F₁ = F₂) (h₀₂ : F₀ = F₂) (e : F₂ ≅ F₃) :
    (eqToIso (congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up) h₀₁) ≪≫
      smallIso (eqToIso h₁₂)) ≪≫ smallIso e =
        smallIso (eqToIso h₀₂ ≪≫ e) := by
  rw [smallIso_eqToIso, eqToIso_trans, smallIso_trans, smallIso_eqToIso]

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable (k : laurent ⟶ polynomial)
  (hk : ∀ V, k.app V ≫ projection.app V = laurentProjection.app V)

/-- The original polynomial column anchor inside the second-arrow input surface. -/
abbrev polynomialAnchor := ProjectionRectangleSquareRows.polynomialAnchor
  (projection.app Z) (k.app Z) (k.app Y) (polynomial.map g) (laurent.map g)
  (k.naturality g) (laurentProjection.app Z) (hk Z)

/-- The actual chart naturality and projection give the unchanged middle-column total. -/
abbrev columnGeom := projection_middle_geom (projection.app Z) (k.app Z) (k.app Y)
  (polynomial.map g) (laurent.map g) (k.naturality g) (laurentProjection.app Z) (hk Z)

/-- The whole original polynomial-column anchor has its exact geometric normalized form. -/
theorem polynomial_anchor_normal : polynomialAnchor g k hk =
    smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (columnGeom g k hk)) ≪≫
      boundedFlatNormalizedPullbackCompIso (k.app Y) (polynomial.map g ≫ projection.app Z)) := by
  exact smallIso_transport_trans
    (congrArg boundedFlatNormalizedPullback
      (congrArg (fun r ↦ laurent.map g ≫ r) (hk Z).symm))
    (congrArg boundedFlatNormalizedPullback
      (DoubleSquareTrack.middle_eq (projection.app Z) (k.app Z) (k.app Y)
        (polynomial.map g) (laurent.map g) (k.naturality g)).symm)
    (congrArg boundedFlatNormalizedPullback (columnGeom g k hk))
    (boundedFlatNormalizedPullbackCompIso (k.app Y) (polynomial.map g ≫ projection.app Z))

/-- The identical actual postmap of every polynomial-column node. -/
abbrev columnPostmap := arrow (k.app Y) ≫ arrow (laurent.map f)

/-- The full original first-component anchor includes Laurent postcomposition. -/
def firstAnchor := postAnchor f g ≪≫
  isoWhiskerRight (polynomialAnchor g k hk) (arrow (laurent.map f)).functor

/-- The product column retains the original normalized chart target-node reference. -/
def productAnchor := sourceIso f g k hk ≪≫
  isoWhiskerLeft (polynomialSource g).functor (chartNodes f k 2).2

/-- Actual three-factor normalization identifies the complete first and product anchors. -/
theorem column_reference : firstAnchor f g k hk = productAnchor f g k hk := by
  change postAnchor f g ≪≫
    isoWhiskerRight (polynomialAnchor g k hk) (arrow (laurent.map f)).functor =
    sourceIso f g k hk ≪≫ isoWhiskerLeft (polynomialSource g).functor
      (chartNodes f k 2).2
  rw [polynomial_anchor_normal]
  change smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (post_total f g).symm) ≪≫
      boundedFlatNormalizedPullbackCompIso (laurent.map f)
        (laurent.map g ≫ laurentProjection.app Z)) ≪≫
    isoWhiskerRight
      (smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (columnGeom g k hk)) ≪≫
        boundedFlatNormalizedPullbackCompIso (k.app Y) (polynomial.map g ≫ projection.app Z)))
      (AsSmall.down ⋙ boundedFlatNormalizedPullback (laurent.map f) ⋙ AsSmall.up) =
    smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (total f g k hk).symm) ≪≫
      boundedFlatNormalizedPullbackCompIso (laurent.map f ≫ k.app Y)
        (polynomial.map g ≫ projection.app Z)) ≪≫
    isoWhiskerLeft
      (AsSmall.down ⋙ boundedFlatNormalizedPullback (polynomial.map g ≫ projection.app Z) ⋙
        AsSmall.up)
      (smallIso (boundedFlatNormalizedPullbackCompIso (laurent.map f) (k.app Y)))
  rw [smallIso_postcomp, smallIso_precomp, ← smallIso_trans, ← smallIso_trans]
  apply congrArg smallIso
  simpa only [eqToIso_refl, Iso.refl_trans, Iso.trans_assoc] using
    (anchored_factorizations_strict (laurent.map f) (k.app Y)
      (polynomial.map g ≫ projection.app Z) (laurent.map f ≫ k.app Y)
      (laurent.map g ≫ laurentProjection.app Z)
      (laurent.map (f ≫ g) ≫ laurentProjection.app Z)
      rfl (columnGeom g k hk) (total f g k hk).symm (post_total f g).symm).symm

/-- All original polynomial nodes keep both actual postcomposition references. -/
theorem first_column (i : Fin 5) :
    postNode f g (InputDescSimplex.chartNodes g k hk
      (ProjectionRectangleSquareRows.polynomialRow i)) =
    postReferenceNode (InputCompositionCarrierCharts.source f g) (columnPostmap f k)
      (H := polynomialSource g) (firstAnchor f g k hk) (polynomialNodes g i) := by
  have h := congrArg (postNode f g)
    (ProjectionRectangleSquareRows.polynomial_row_nodes
      (projection.app Z) (k.app Z) (projection.app Y) (k.app Y)
      g (polynomial.map g) (laurent.map g) (projection.naturality g) (k.naturality g)
      (laurentProjection.app Z) (hk Z) i)
  exact h.trans (post_post_node (InputCompositionCarrierCharts.source f g)
    (arrow (k.app Y)) (arrow (laurent.map f)) (polynomialSource g)
    (polynomialAnchor g k hk) (postAnchor f g) (polynomialNodes g i))

/-- The entire actual product column keeps the identical original polynomial-node family. -/
theorem product_column (i : Fin 5) :
    nodes f g k hk (Quillen.SimplexGrid.index 4 4 (i, 2)) =
    postReferenceNode (InputCompositionCarrierCharts.source f g) (columnPostmap f k)
      (H := polynomialSource g) (productAnchor f g k hk) (polynomialNodes g i) :=
  product_column_nodes (InputCompositionCarrierCharts.source f g) (polynomialSource g)
    (fun j ↦ (polynomialNodes g j).1) (fun j ↦ (polynomialNodes g j).2)
    (chartSource f k) (fun j ↦ (chartNodes f k j).1) (fun j ↦ (chartNodes f k j).2)
    (sourceIso f g k hk) i 2

/-- The five complete first/product boundary nodes agree for either actual original chart. -/
theorem column_nodes (i : Fin 5) :
    postNode f g (InputDescSimplex.chartNodes g k hk
      (ProjectionRectangleSquareRows.polynomialRow i)) =
      nodes f g k hk (Quillen.SimplexGrid.index 4 4 (i, 2)) := by
  rw [first_column, column_reference]
  exact (product_column f g k hk i).symm

end Quillen.PerfectComplexes.GlobalRawBass.InputCompositionTerminalColumns
