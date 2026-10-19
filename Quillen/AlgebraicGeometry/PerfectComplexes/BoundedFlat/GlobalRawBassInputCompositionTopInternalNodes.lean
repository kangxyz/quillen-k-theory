/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputCompositionTopPieces
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MReferenceAlgebra
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.PostReferenceFamily

/-!
# Full internal nodes of the original global composition vertex stage

The original positive and inverse polynomial moving columns agree with their actual middle
product columns, including the complete reference isomorphisms. The only coherence used is
normalized-pullback associativity on the original scheme arrows and their projection equalities.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen.IteratedS
open Quillen.PerfectComplexes.BassReferenceMerge Quillen.PerfectComplexes.BassH0Merge
open Quillen.PerfectComplexes.BassH1Join Quillen.PerfectComplexes.BassMJoin
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace Quillen.PerfectComplexes.GlobalRawBass.InputCompositionTopInternalNodes
open InputCompositionTopPieces
private theorem full_node_eq {V W : Model.{u}} {F : V ⟶ W}
    (N M : CommonReferenceNerve.Node F) (hf : N.1.functor = M.1.functor)
    (hr : HEq N.2 M.2) : N = M :=
  Sigma.ext (Model.Hom.ext hf) hr

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable (k : laurent ⟶ polynomial)
  (hk : ∀ V, k.app V ≫ projection.app V = laurentProjection.app V)

/-- The complete original base-composition column in the unmodified polynomial moving diagram. -/
theorem polynomial_base_column (i : Fin 3) :
    polynomialNodes f g (DoubleSquareMergedSimplex.firstFace.toOrderHom (leftIndex i)) =
    postReferenceNode (H := baseSource f g)
      (polynomialSource f g) (normalizedMap (projection.app X))
      (BinaryNormalizationSimplex.total (projection.app X)
        (f ≫ g)) (binaryNodes f g i) := by
  have hn : polynomialNodes f g
      (DoubleSquareMergedSimplex.firstFace.toOrderHom (leftIndex i)) =
      tripleLeftNode (polynomialSource f g) (projection.app X)
        f g rfl i := by
    fin_cases i <;> rfl
  exact hn.trans (triple_left_column (polynomialSource f g) (projection.app X)
    f g rfl i)

/-- The original polynomial projection followed by the original target chart map. -/
abbrev endpointMap := normalizedMap (projection.app X) ≫
  normalizedMap (k.app X)

/-- The actual moving-square anchor on its base-composition edge. -/
def movingColumnIso : (InputCompositionCarrierCharts.source f g).functor ≅
    (baseSource f g ≫ endpointMap (X := X) k).functor :=
  movingAnchor f g k hk ≪≫ isoWhiskerRight
    (BinaryNormalizationSimplex.total (projection.app X)
      (f ≫ g))
    (normalizedMap (k.app X)).functor

/-- The actual positive or inverse projection endpoint, including its literal source transport. -/
def projectionEndpointIso : (InputIdentityProjection.source X).functor ≅
    (endpointMap (X := X) k).functor :=
  smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
    ((plus_projection X).trans (hk X).symm)) ≪≫
      boundedFlatNormalizedPullbackCompIso (k.app X) (projection.app X))

/-- The actual product anchor at the specified original projection endpoint. -/
def productColumnIso : (InputCompositionCarrierCharts.source f g).functor ≅
    (baseSource f g ≫ endpointMap (X := X) k).functor :=
  middleAnchor f g ≪≫ isoWhiskerLeft (baseSource f g).functor
    (projectionEndpointIso (X := X) k hk)

/-- The entire moving base-composition column retains its full reference under the chart map. -/
theorem moving_base_column (i : Fin 3) :
    movingNodes f g k hk
      (DoubleSquareMergedSimplex.firstFace.toOrderHom (leftIndex i)) =
    postReferenceNode (H := baseSource f g)
      (InputCompositionCarrierCharts.source f g) (endpointMap (X := X) k)
      (movingColumnIso f g k hk) (binaryNodes f g i) := by
  have hn := congrArg (postReferenceNode (InputCompositionCarrierCharts.source f g)
    (normalizedMap (k.app X)) (movingAnchor f g k hk))
      (polynomial_base_column f g i)
  exact hn.trans (post_post_node (InputCompositionCarrierCharts.source f g)
    (normalizedMap (projection.app X)) (normalizedMap (k.app X))
    (baseSource f g) _ (movingAnchor f g k hk) (binaryNodes f g i))

/-- Original normalized pullback associativity identifies the two complete boundary references. -/
theorem internal_reference : movingColumnIso f g k hk = productColumnIso f g k hk := by
  exact small_anchored_factorization (k.app X) (projection.app X)
    (f ≫ g)
    (plus.app X ≫ projection.app X)
    (laurent.map (f ≫ g) ≫ laurentProjection.app Z)
    ((plus_projection X).trans (hk X).symm)
    (middle_total f g).symm (moving_total f g k hk).symm

/-- The actual positive projection endpoint has exactly its normalization reference. -/
theorem plus_endpoint_node : InputIdentityProjection.nodes X 2 =
    ⟨endpointMap (X := X) plus,
      projectionEndpointIso (X := X) plus plus_projection⟩ := by
  have hf : (InputIdentityProjection.nodes X 2).1.functor =
      (endpointMap (X := X) plus).functor := rfl
  apply full_node_eq (InputIdentityProjection.nodes X 2)
    ⟨endpointMap (X := X) plus, projectionEndpointIso (X := X) plus plus_projection⟩ hf
  exact heq_of_eq (small_binary_refl (plus.app X) (projection.app X)
    ((plus_projection X).trans (plus_projection X).symm))

/-- The inverse endpoint retains the actual equality transport between the two projections. -/
theorem minus_endpoint_node : InputIdentityProjection.nodes X 4 =
    ⟨endpointMap (X := X) minus,
      projectionEndpointIso (X := X) minus minus_projection⟩ := by
  have hf : (InputIdentityProjection.nodes X 4).1.functor =
      (endpointMap (X := X) minus).functor := rfl
  apply full_node_eq (InputIdentityProjection.nodes X 4)
    ⟨endpointMap (X := X) minus, projectionEndpointIso (X := X) minus minus_projection⟩ hf
  exact heq_of_eq (small_binary_transport (plus.app X ≫ projection.app X)
    (minus.app X) (projection.app X)
    ((plus_projection X).trans (minus_projection X).symm))

private theorem base_node (i : Fin 3) :
    (⟨baseVertices f g i, baseReferences f g i⟩ : CommonReferenceNerve.Node (baseSource f g)) =
      binaryNodes f g i := by
  fin_cases i <;> rfl

/-- The original product endpoint column retains its base-composition row and full anchor. -/
theorem product_endpoint_column (j : Fin 5)
    (hj : InputIdentityProjection.nodes X j =
      ⟨endpointMap (X := X) k, projectionEndpointIso (X := X) k hk⟩)
    (i : Fin 3) :
    middleNodes f g (Quillen.SimplexGrid.index 2 4 (i, j)) =
    postReferenceNode (H := baseSource f g)
      (InputCompositionCarrierCharts.source f g) (endpointMap (X := X) k)
      (productColumnIso f g k hk) (binaryNodes f g i) := by
  have hn := product_column_nodes (InputCompositionCarrierCharts.source f g)
    (baseSource f g) (baseVertices f g) (baseReferences f g)
    (InputIdentityProjection.source X) (fun i ↦ (InputIdentityProjection.nodes X i).1)
    (fun i ↦ (InputIdentityProjection.nodes X i).2) (middleAnchor f g) i j
  change _ = postReferenceNode (InputCompositionCarrierCharts.source f g)
    (InputIdentityProjection.nodes X j).1
    (middleAnchor f g ≪≫ isoWhiskerLeft (baseSource f g).functor
      (InputIdentityProjection.nodes X j).2)
      ⟨baseVertices f g i, baseReferences f g i⟩ at hn
  rw [hj] at hn
  exact hn.trans (congrArg (postReferenceNode (InputCompositionCarrierCharts.source f g)
    (endpointMap (X := X) k) (productColumnIso f g k hk)) (base_node f g i))

/-- Every full original positive internal boundary node, including the raw intermediate, agrees. -/
theorem plus_internal_nodes (i : Fin 3) :
    movingNodes f g plus plus_projection
      (DoubleSquareMergedSimplex.firstFace.toOrderHom (leftIndex i)) =
    middleNodes f g (Quillen.SimplexGrid.index 2 4 (i, 2)) := by
  rw [moving_base_column, internal_reference]
  exact (product_endpoint_column f g plus plus_projection
    2 (plus_endpoint_node (X := X)) i).symm

/-- Every inverse internal boundary node agrees with its separate original chart reference. -/
theorem minus_internal_nodes (i : Fin 3) :
    movingNodes f g minus minus_projection
      (DoubleSquareMergedSimplex.firstFace.toOrderHom (leftIndex i)) =
    middleNodes f g (Quillen.SimplexGrid.index 2 4 (i, 4)) := by
  rw [moving_base_column, internal_reference]
  exact (product_endpoint_column f g minus minus_projection
    4 (minus_endpoint_node (X := X)) i).symm

end Quillen.PerfectComplexes.GlobalRawBass.InputCompositionTopInternalNodes
