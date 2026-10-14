/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MChartSideRows

/-! Full original row representations for the first path of the target reassociation word. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.PolynomialBaseChange Quillen.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassMOuterJoin
open BassH0Merge BassH1Join BassMComponents BassMReferences
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)
variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (hb : coefficientMap P (α.app b) ≫ polynomialProjection P b = laurentProjection P b)
  (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)

abbrev polynomialMiddleIso := DoubleSquareCommonSimplex.middleSourceIso
  (coefficientMap P u) (coefficientMap P v)
  (coefficientMap P ((polynomialUnderFunctor R).map v))
  (polynomialProjection P b) (polynomialProjection P c)
  (coefficientTransformation_naturality P (polynomialUnderCoefficient R) v).symm

abbrev targetPost := normalizedMap (coefficientMap P ((polynomialUnderFunctor R).map v)) ≫
  normalizedMap (coefficientMap P (α.app c))

def movingFirstTargetIso := movingIso P u v α hc ≪≫ isoWhiskerRight
  (polynomialLastIso P u v ≪≫ BinaryNormalizationSimplex.total
    (coefficientMap P ((polynomialUnderFunctor R).map v))
    (coefficientMap P ((polynomialUnderFunctor R).map u) ≫ polynomialProjection P a))
  (normalizedMap (coefficientMap P (α.app c))).functor

def movingSecondTargetIso := movingIso P u v α hc ≪≫ isoWhiskerRight
  (polynomialMiddleIso P u v ≪≫ BinaryNormalizationSimplex.total
    (coefficientMap P ((polynomialUnderFunctor R).map v))
    (polynomialProjection P b ≫ coefficientMap P u))
  (normalizedMap (coefficientMap P (α.app c))).functor

def productTargetIso := BassH1References.chartIso P u v α hb ≪≫
  isoWhiskerLeft (CoefficientSquareFamilies.polynomialSource P u).functor
    (CoefficientSquareFamilies.chartNodes P v α 4).2

/-- The first native target row is the original u-square triangle after both fixed target maps. -/
theorem moving_first_target_row (i : Fin 3) :
    movingNodes P u v α hc (DoubleSquareMergedSimplex.lastFace.toOrderHom (leftIndex i)) =
    postReferenceNode (BassOverlap.commonReference P u v) (targetPost P v α)
      (movingFirstTargetIso P u v α hc)
      (binaryNodes (coefficientMap P ((polynomialUnderFunctor R).map u))
        (polynomialProjection P a) i) := by
  have hn := congrArg (postReferenceNode (BassOverlap.commonReference P u v)
    (normalizedMap (coefficientMap P (α.app c))) (movingIso P u v α hc))
    (rectangle_last_left_nodes (coefficientMap P u) (coefficientMap P v)
      (coefficientMap P ((polynomialUnderFunctor R).map u))
      (coefficientMap P ((polynomialUnderFunctor R).map v))
      (polynomialProjection P a) (polynomialProjection P b) (polynomialProjection P c)
      (coefficientTransformation_naturality P (polynomialUnderCoefficient R) u).symm
      (coefficientTransformation_naturality P (polynomialUnderCoefficient R) v).symm i)
  exact hn.trans (post_post_node (BassOverlap.commonReference P u v)
    (normalizedMap (coefficientMap P ((polynomialUnderFunctor R).map v)))
    (normalizedMap (coefficientMap P (α.app c)))
    (CoefficientSquareFamilies.polynomialSource P u) _ (movingIso P u v α hc) _)

/-- The other original u-square triangle retains the middle source transport under both maps. -/
theorem moving_second_target_row (i : Fin 3) :
    movingNodes P u v α hc (DoubleSquareMergedSimplex.middleFace.toOrderHom (leftIndex i)) =
    postReferenceNode (BassOverlap.commonReference P u v) (targetPost P v α)
      (movingSecondTargetIso P u v α hc)
      (binaryNodes (polynomialProjection P b) (coefficientMap P u) i) := by
  have hn := congrArg (postReferenceNode (BassOverlap.commonReference P u v)
    (normalizedMap (coefficientMap P (α.app c))) (movingIso P u v α hc))
    (rectangle_middle_left_nodes (coefficientMap P u) (coefficientMap P v)
      (coefficientMap P ((polynomialUnderFunctor R).map u))
      (coefficientMap P ((polynomialUnderFunctor R).map v))
      (polynomialProjection P a) (polynomialProjection P b) (polynomialProjection P c)
      (coefficientTransformation_naturality P (polynomialUnderCoefficient R) u).symm
      (coefficientTransformation_naturality P (polynomialUnderCoefficient R) v).symm i)
  exact hn.trans (post_post_node (BassOverlap.commonReference P u v)
    (normalizedMap (coefficientMap P ((polynomialUnderFunctor R).map v)))
    (normalizedMap (coefficientMap P (α.app c)))
    (BinaryNormalizationSimplex.sourceMap (polynomialProjection P b) (coefficientMap P u))
    _ (movingIso P u v α hc) _)

/-- The product target column is the original polynomial square after its target map. -/
theorem product_target_column (i : Fin 5) :
    BassH1References.chartNodes P u v α hb (Quillen.SimplexGrid.index 4 4 (i, 4)) =
    postReferenceNode (BassOverlap.commonReference P u v) (targetPost P v α)
      (productTargetIso P u v α hb) (CoefficientSquareFamilies.polynomialNodes P u i) :=
  product_column_nodes (BassOverlap.commonReference P u v)
    (CoefficientSquareFamilies.polynomialSource P u)
    (fun i ↦ (CoefficientSquareFamilies.polynomialNodes P u i).1)
    (fun i ↦ (CoefficientSquareFamilies.polynomialNodes P u i).2)
    (CoefficientSquareFamilies.chartSource P v α)
    (fun i ↦ (CoefficientSquareFamilies.chartNodes P v α i).1)
    (fun i ↦ (CoefficientSquareFamilies.chartNodes P v α i).2)
    (BassH1References.chartIso P u v α hb) i 4

/-- The product first target row retains every original first binary normalization node. -/
theorem product_first_target_row (i : Fin 3) :
    BassH1References.chartNodes P u v α hb
      (Quillen.SimplexGrid.index 4 4 (NativeSquareFiveSimplex.firstFace.toOrderHom i, 4)) =
    postReferenceNode (BassOverlap.commonReference P u v) (targetPost P v α)
      (productTargetIso P u v α hb)
      (binaryNodes (coefficientMap P ((polynomialUnderFunctor R).map u))
        (polynomialProjection P a) i) :=
  (product_target_column P u v α hb _).trans (post_square_first_nodes
    (coefficientMap P ((polynomialUnderFunctor R).map u)) (polynomialProjection P a)
    (polynomialProjection P b) (coefficientMap P u)
    (coefficientTransformation_naturality P (polynomialUnderCoefficient R) u)
    (BassOverlap.commonReference P u v) (targetPost P v α) (productTargetIso P u v α hb) i)

/-- The product second target row retains its actual polynomial-square source equality. -/
theorem product_second_target_row (i : Fin 3) :
    BassH1References.chartNodes P u v α hb
      (Quillen.SimplexGrid.index 4 4 (NativeSquareFiveSimplex.secondFace.toOrderHom i, 4)) =
    postReferenceNode (BassOverlap.commonReference P u v) (targetPost P v α)
      (productTargetIso P u v α hb ≪≫ isoWhiskerRight
        (NativeSquareFiveSimplex.sourceIso
          (coefficientMap P ((polynomialUnderFunctor R).map u)) (polynomialProjection P a)
          (polynomialProjection P b) (coefficientMap P u)
          (coefficientTransformation_naturality P (polynomialUnderCoefficient R) u))
        (targetPost P v α).functor)
      (binaryNodes (polynomialProjection P b) (coefficientMap P u) i) :=
  (product_target_column P u v α hb _).trans (post_square_second_nodes
    (coefficientMap P ((polynomialUnderFunctor R).map u)) (polynomialProjection P a)
    (polynomialProjection P b) (coefficientMap P u)
    (coefficientTransformation_naturality P (polynomialUnderCoefficient R) u)
    (BassOverlap.commonReference P u v) (targetPost P v α) (productTargetIso P u v α hb) i)

end Quillen.PerfectComplexes.BassMOuterJoin
