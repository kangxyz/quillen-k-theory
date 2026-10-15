/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MSecondTargetNodes

/-! Full original projection-row forms on the inter-stage middle boundary. -/
@[expose] public section

open Quillen.PerfectComplexes.BassH0Merge
open Quillen.PerfectComplexes.BassH1Join
open Quillen.PerfectComplexes.BassMComponents
open Quillen.PerfectComplexes.BassMReferences


open CommRingCat.PolynomialLaurent

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassMOuterJoin
open BassH0Merge BassH1Join BassMComponents BassMReferences
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/--
The composite of the normalized coefficient maps of `u` and `v`, used to precompose the target
projection row.
-/
abbrev targetMiddlePre := normalizedMap (coefficientMap P u) ≫ normalizedMap (coefficientMap P v)

/--
The target projection-row reference, combining the middle reference with binary normalization of
the coefficient composite.
-/
def targetMiddleIso := middleIso P u v ≪≫
  isoWhiskerRight (BinaryNormalizationSimplex.total (coefficientMap P v) (coefficientMap P u))
    (BassProjectionPath.source P c).functor

/--
The inverse projection-row reference, obtained from `targetMiddleIso` by the projection source
isomorphism.
-/
def targetMiddleMinusIso := targetMiddleIso P u v ≪≫
  isoWhiskerLeft (targetMiddlePre P u v).functor (BassProjectionPath.sourceIso P c)

/-- The product target row retains the actual composition of both original coefficient maps. -/
theorem middle_target_row (j : Fin 5) :
    middleNodes P u v (Quillen.SimplexGrid.index 2 4 (2, j)) =
    preReferenceNode (BassOverlap.commonReference P u v) (targetMiddlePre P u v)
      (targetMiddleIso P u v) (BassProjectionPath.nodes P c j) :=
  product_row_nodes (BassOverlap.commonReference P u v)
    (coefficientSource P u v) (fun i ↦ (coefficientNodes P u v i).1)
    (fun i ↦ (coefficientNodes P u v i).2)
    (BassProjectionPath.source P c) (fun i ↦ (BassProjectionPath.nodes P c i).1)
    (fun i ↦ (BassProjectionPath.nodes P c i).2) (middleIso P u v) 2 j

/-- Every positive target-row node retains its original binary projection normalization. -/
theorem middle_target_plus_row (i : Fin 3) :
    middleNodes P u v (Quillen.SimplexGrid.index 2 4 (2, Fin.castAdd 2 i)) =
    preReferenceNode (BassOverlap.commonReference P u v) (targetMiddlePre P u v)
      (targetMiddleIso P u v) (binaryNodes (laurentPlus P c) (polynomialProjection P c) i) := by
  rw [middle_target_row, projection_plus_nodes P (a := c)]

/-- Every inverse target-row node retains the actual separate projection source transport. -/
theorem middle_target_minus_row (i : Fin 3) :
    middleNodes P u v
      (Quillen.SimplexGrid.index 2 4 (2, BassProjectionPath.minusFace.toOrderHom i)) =
    preReferenceNode (BassOverlap.commonReference P u v) (targetMiddlePre P u v)
      (targetMiddleMinusIso P u v)
      (binaryNodes (laurentMinus P c) (polynomialProjection P c) i) := by
  rw [middle_target_row, projection_minus_all]
  exact pre_anchor_node (BassOverlap.commonReference P u v) (targetMiddlePre P u v)
    (targetMiddleIso P u v) (BassProjectionPath.sourceIso P c)
    (binaryNodes (laurentMinus P c) (polynomialProjection P c) i)

variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (hb : coefficientMap P (α.app b) ≫ polynomialProjection P b = laurentProjection P b)

/--
The H1 target projection-row reference, with the normalized coefficient map of `u` precomposed
onto the target-row reference for `v`.
-/
def h1TargetProjectionIso := BassH1References.middleIso P u v ≪≫
  isoWhiskerLeft (normalizedMap (coefficientMap P u)).functor
    (BassH1H0Boundary.targetRowReference P v α hb)

/-- H1's middle target row keeps its two actual coefficient precompositions and full references. -/
theorem h1_target_projection_row (i : Fin 3) :
    h1MiddleChartNodes P u v α hb
      (DoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i)) =
    preReferenceNode (H := BinaryNormalizationSimplex.sourceMap
      (coefficientMap P (α.app c)) (polynomialProjection P c))
      (BassOverlap.commonReference P u v) (targetMiddlePre P u v)
      (h1TargetProjectionIso P u v α hb)
      (binaryNodes (coefficientMap P (α.app c)) (polynomialProjection P c) i) := by
  have hn := congrArg (preReferenceNode (BassOverlap.commonReference P u v)
    (normalizedMap (coefficientMap P u)) (BassH1References.middleIso P u v))
      (BassH1H0Boundary.chart_target_row P v α hb i)
  exact hn.trans (pre_pre_node (BassOverlap.commonReference P u v)
    (normalizedMap (coefficientMap P u)) (normalizedMap (coefficientMap P v))
    (BinaryNormalizationSimplex.sourceMap (coefficientMap P (α.app c)) (polynomialProjection P c))
    (BassH1H0Boundary.targetRowReference P v α hb) (BassH1References.middleIso P u v)
    (binaryNodes (coefficientMap P (α.app c)) (polynomialProjection P c) i))

end Quillen.PerfectComplexes.BassMOuterJoin
