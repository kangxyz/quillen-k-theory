/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MComponentReferences
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MReferenceAlgebra

/-! Full original reference identities on both internal M vertex-stage boundaries. -/
@[expose] public section

open Quillen.PerfectComplexes.BassH0Merge
open Quillen.PerfectComplexes.BassH1Join
open Quillen.PerfectComplexes.BassMComponents
open Quillen.PerfectComplexes.BassMReferences
open Quillen.PerfectComplexes.BassReferenceMerge


open CommRingCat.PolynomialLaurent

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassMJoin
open BassReferenceMerge BassH0Merge BassH1Join BassMComponents BassMReferences
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)
variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)

/-- The complete original coefficient column in the unmodified polynomial moving diagram. -/
theorem polynomial_coefficient_column (i : Fin 3) :
    polynomialNodes P u v (DoubleSquareMergedSimplex.firstFace.toOrderHom (leftIndex i)) =
    postReferenceNode (H := coefficientSource P u v)
      (polynomialSource P u v) (normalizedMap (polynomialProjection P c))
      (BinaryNormalizationSimplex.total (polynomialProjection P c)
        (coefficientMap P v ≫ coefficientMap P u)) (coefficientNodes P u v i) := by
  have hn : polynomialNodes P u v
      (DoubleSquareMergedSimplex.firstFace.toOrderHom (leftIndex i)) =
      tripleLeftNode (polynomialSource P u v) (polynomialProjection P c)
        (coefficientMap P v) (coefficientMap P u) rfl i := by
    fin_cases i <;> rfl
  exact hn.trans (triple_left_column (polynomialSource P u v) (polynomialProjection P c)
    (coefficientMap P v) (coefficientMap P u) rfl i)

/--
The normalized polynomial projection at `c` followed by the normalized chart coefficient map at
`c`.
-/
abbrev endpointMap := normalizedMap (polynomialProjection P c) ≫
  normalizedMap (coefficientMap P (α.app c))

/-- The actual moving-square anchor on its coefficient-composition edge. -/
def movingColumnIso : (BassOverlap.commonReference P u v).functor ≅
    (coefficientSource P u v ≫ endpointMap P α).functor :=
  movingIso P u v α hc ≪≫ isoWhiskerRight
    (BinaryNormalizationSimplex.total (polynomialProjection P c)
      (coefficientMap P v ≫ coefficientMap P u))
    (normalizedMap (coefficientMap P (α.app c))).functor

/-- The actual positive or inverse projection endpoint, including its literal source transport. -/
def projectionEndpointIso : (BassProjectionPath.source P c).functor ≅
    (endpointMap P α).functor :=
  smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
    ((laurentPlus_projection P c).trans hc.symm)) ≪≫
      boundedFlatNormalizedPullbackCompIso (coefficientMap P (α.app c)) (polynomialProjection P c))

/-- The actual product anchor at the specified original projection endpoint. -/
def productColumnIso : (BassOverlap.commonReference P u v).functor ≅
    (coefficientSource P u v ≫ endpointMap P α).functor :=
  middleIso P u v ≪≫ isoWhiskerLeft (coefficientSource P u v).functor
    (projectionEndpointIso P α hc)

/-- The entire moving coefficient column retains its full reference under the chart map. -/
theorem moving_coefficient_column (i : Fin 3) :
    movingNodes P u v α hc
      (DoubleSquareMergedSimplex.firstFace.toOrderHom (leftIndex i)) =
    postReferenceNode (H := coefficientSource P u v)
      (BassOverlap.commonReference P u v) (endpointMap P α)
      (movingColumnIso P u v α hc) (coefficientNodes P u v i) := by
  have hn := congrArg (postReferenceNode (BassOverlap.commonReference P u v)
    (normalizedMap (coefficientMap P (α.app c))) (movingIso P u v α hc))
      (polynomial_coefficient_column P u v i)
  exact hn.trans (post_post_node (BassOverlap.commonReference P u v)
    (normalizedMap (polynomialProjection P c)) (normalizedMap (coefficientMap P (α.app c)))
    (coefficientSource P u v) _ (movingIso P u v α hc) (coefficientNodes P u v i))

/-- Original normalized pullback associativity identifies the two complete boundary references. -/
theorem internal_reference : movingColumnIso P u v α hc = productColumnIso P u v α hc := by
  exact small_anchored_factorization (coefficientMap P (α.app c)) (polynomialProjection P c)
    (coefficientMap P v ≫ coefficientMap P u)
    (laurentPlus P c ≫ polynomialProjection P c)
    (laurentProjection P c ≫ coefficientMap P v ≫ coefficientMap P u)
    ((laurentPlus_projection P c).trans hc.symm)
    (middle_total P u v).symm (moving_total P u v α hc).symm

/-- The actual positive projection endpoint has exactly its normalization reference. -/
theorem plus_endpoint_node : BassProjectionPath.nodes P c 2 =
    ⟨endpointMap P (underToLaurent R),
      projectionEndpointIso P (underToLaurent R) (laurentPlus_projection P c)⟩ := by
  have hf : (BassProjectionPath.nodes P c 2).1 = endpointMap P (underToLaurent R) :=
    Model.Hom.ext rfl
  apply Sigma.ext hf
  exact heq_of_eq (small_binary_refl (laurentPlus P c) (polynomialProjection P c)
    ((laurentPlus_projection P c).trans (laurentPlus_projection P c).symm))

/-- The inverse endpoint retains the actual equality transport between the two projections. -/
theorem minus_endpoint_node : BassProjectionPath.nodes P c 4 =
    ⟨endpointMap P (underToLaurentInvert R),
      projectionEndpointIso P (underToLaurentInvert R) (laurentMinus_projection P c)⟩ := by
  have hf : (BassProjectionPath.nodes P c 4).1 = endpointMap P (underToLaurentInvert R) :=
    Model.Hom.ext rfl
  apply Sigma.ext hf
  exact heq_of_eq (small_binary_transport (laurentPlus P c ≫ polynomialProjection P c)
    (laurentMinus P c) (polynomialProjection P c)
    ((laurentPlus_projection P c).trans (laurentMinus_projection P c).symm))

/-- A complete original product endpoint column has the same coefficient row and full anchor. -/
theorem product_endpoint_column (j : Fin 5)
    (hj : BassProjectionPath.nodes P c j = ⟨endpointMap P α, projectionEndpointIso P α hc⟩)
    (i : Fin 3) :
    middleNodes P u v (Quillen.SimplexGrid.index 2 4 (i, j)) =
    postReferenceNode (H := coefficientSource P u v)
      (BassOverlap.commonReference P u v) (endpointMap P α)
      (productColumnIso P u v α hc) (coefficientNodes P u v i) := by
  have hn := product_column_nodes (BassOverlap.commonReference P u v)
    (coefficientSource P u v) (fun i ↦ (coefficientNodes P u v i).1)
    (fun i ↦ (coefficientNodes P u v i).2)
    (BassProjectionPath.source P c) (fun i ↦ (BassProjectionPath.nodes P c i).1)
    (fun i ↦ (BassProjectionPath.nodes P c i).2) (middleIso P u v) i j
  change _ = postReferenceNode (BassOverlap.commonReference P u v)
    (BassProjectionPath.nodes P c j).1
    (middleIso P u v ≪≫ isoWhiskerLeft (coefficientSource P u v).functor
      (BassProjectionPath.nodes P c j).2) (coefficientNodes P u v i) at hn
  rw [hj] at hn
  exact hn

/-- Every full original positive internal boundary node, including the raw intermediate, agrees. -/
theorem plus_internal_nodes (i : Fin 3) :
    movingNodes P u v (underToLaurent R) (laurentPlus_projection P c)
      (DoubleSquareMergedSimplex.firstFace.toOrderHom (leftIndex i)) =
    middleNodes P u v (Quillen.SimplexGrid.index 2 4 (i, 2)) := by
  rw [moving_coefficient_column, internal_reference]
  exact (product_endpoint_column P u v (underToLaurent R) (laurentPlus_projection P c)
    2 (plus_endpoint_node P) i).symm

/-- Every inverse internal boundary node agrees with its separate original chart reference. -/
theorem minus_internal_nodes (i : Fin 3) :
    movingNodes P u v (underToLaurentInvert R) (laurentMinus_projection P c)
      (DoubleSquareMergedSimplex.firstFace.toOrderHom (leftIndex i)) =
    middleNodes P u v (Quillen.SimplexGrid.index 2 4 (i, 4)) := by
  rw [moving_coefficient_column, internal_reference]
  exact (product_endpoint_column P u v (underToLaurentInvert R) (laurentMinus_projection P c)
    4 (minus_endpoint_node P) i).symm

end Quillen.PerfectComplexes.BassMJoin
