/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MRectangleRows

/-! Full actual M/chart side rows from the proved original source corner nodes. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.PolynomialBaseChange AlgebraicGeometry.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassMOuterJoin
open BassH0Merge BassH1Join BassMComponents BassMReferences
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)
variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)

abbrev polynomialLastIso := DoubleSquareCommonSimplex.lastSourceIso
  (coefficientMap P u) (coefficientMap P v)
  (coefficientMap P ((polynomialUnderFunctor R).map u))
  (coefficientMap P ((polynomialUnderFunctor R).map v))
  (polynomialProjection P a) (polynomialProjection P b) (polynomialProjection P c)
  (coefficientTransformation_naturality P (polynomialUnderCoefficient R) u).symm
  (coefficientTransformation_naturality P (polynomialUnderCoefficient R) v).symm

abbrev sideBinarySource := BinaryNormalizationSimplex.sourceMap
  (coefficientMap P ((polynomialUnderFunctor R).map v))
  (coefficientMap P ((polynomialUnderFunctor R).map u))
abbrev sideBinaryNodes := binaryNodes
  (coefficientMap P ((polynomialUnderFunctor R).map v))
  (coefficientMap P ((polynomialUnderFunctor R).map u))

abbrev movingSideBaseIso := rightRowReference (polynomialSource P u v)
  (coefficientMap P ((polynomialUnderFunctor R).map v))
  (coefficientMap P ((polynomialUnderFunctor R).map u)) (polynomialProjection P a)
  (polynomialLastIso P u v)

def movingSideIso := movingIso P u v α hc ≪≫ isoWhiskerRight (movingSideBaseIso P u v)
  (normalizedMap (coefficientMap P (α.app c))).functor

def oldSideIso := BassOverlap.commonToChartReference P u v α hc ≪≫
  isoWhiskerLeft (BassOverlap.projectionMap P (a := a)).functor
    (BinaryNormalizationSimplex.total (coefficientMap P (α.app c))
      (coefficientMap P ((polynomialUnderFunctor R).map v) ≫
        coefficientMap P ((polynomialUnderFunctor R).map u)))

/-- The moving side is the actual original coefficient triangle between the two fixed maps. -/
theorem moving_side_row (i : Fin 3) :
    movingNodes P u v α hc (DoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i)) =
    prePostNodes (BassOverlap.commonReference P u v) (BassOverlap.projectionMap P (a := a))
      (normalizedMap (coefficientMap P (α.app c))) (sideBinarySource P u v)
      (sideBinaryNodes P u v) (movingSideIso P u v α hc) i := by
  have hn := congrArg (postReferenceNode (BassOverlap.commonReference P u v)
    (normalizedMap (coefficientMap P (α.app c))) (movingIso P u v α hc))
    (rectangle_last_right_nodes (coefficientMap P u) (coefficientMap P v)
      (coefficientMap P ((polynomialUnderFunctor R).map u))
      (coefficientMap P ((polynomialUnderFunctor R).map v))
      (polynomialProjection P a) (polynomialProjection P b) (polynomialProjection P c)
      (coefficientTransformation_naturality P (polynomialUnderCoefficient R) u).symm
      (coefficientTransformation_naturality P (polynomialUnderCoefficient R) v).symm i)
  exact hn.trans (post_pre_node (BassOverlap.commonReference P u v)
    (BassOverlap.projectionMap P (a := a)) (normalizedMap (coefficientMap P (α.app c)))
    (sideBinarySource P u v) (sideBinaryNodes P u v) (movingSideBaseIso P u v)
    (movingIso P u v α hc) i)

/-- The old chart side retains the same actual triangle with its original reference route. -/
theorem old_side_row (i : Fin 3) :
    BassOverlap.chartOverlapNodes P u v α hc
      (DoubleSquareMergedSimplex.firstFace.toOrderHom (leftIndex i)) =
    prePostNodes (BassOverlap.commonReference P u v) (BassOverlap.projectionMap P (a := a))
      (normalizedMap (coefficientMap P (α.app c))) (sideBinarySource P u v)
      (sideBinaryNodes P u v) (oldSideIso P u v α hc) i := by
  have hn := congrArg (preReferenceNode (BassOverlap.commonReference P u v)
    (BassOverlap.projectionMap P (a := a)) (BassOverlap.commonToChartReference P u v α hc))
    (rectangle_first_left_nodes
      (coefficientMap P ((polynomialUnderFunctor R).map u))
      (coefficientMap P ((polynomialUnderFunctor R).map v))
      (coefficientMap P ((laurentUnderFunctor R).map u))
      (coefficientMap P ((laurentUnderFunctor R).map v))
      (coefficientMap P (α.app a)) (coefficientMap P (α.app b)) (coefficientMap P (α.app c))
      (coefficientTransformation_naturality P α u).symm
      (coefficientTransformation_naturality P α v).symm i)
  exact hn.trans (pre_post_node (BassOverlap.commonReference P u v)
    (BassOverlap.projectionMap P (a := a)) (normalizedMap (coefficientMap P (α.app c)))
    (sideBinarySource P u v) (sideBinaryNodes P u v)
    (BinaryNormalizationSimplex.total (coefficientMap P (α.app c))
      (coefficientMap P ((polynomialUnderFunctor R).map v) ≫
        coefficientMap P ((polynomialUnderFunctor R).map u)))
    (BassOverlap.commonToChartReference P u v α hc) i)

/-- The positive source corner was already proved in the literal H0/chart and M/H0 boundaries. -/
theorem plus_side_corner : movingNodes P u v (underToLaurent R) (laurentPlus_projection P c) 15 =
    BassOverlap.chartOverlapNodes P u v (underToLaurent R) (laurentPlus_projection P c) 2 :=
  (source_plus_h0_nodes P u v 2).trans
    ((plus_polynomial_rows P u v 2).trans (old_plus_node P u v 2))

/-- The inverse source corner retains the separate actual inverse normalization references. -/
theorem minus_side_corner :
    movingNodes P u v (underToLaurentInvert R) (laurentMinus_projection P c) 15 =
    BassOverlap.chartOverlapNodes P u v (underToLaurentInvert R) (laurentMinus_projection P c) 2 :=
  (source_minus_h0_nodes P u v 2).trans
    ((minus_polynomial_rows P u v 2).trans (old_minus_node P u v 2))

/-- All positive side nodes agree as full original dependent reference nodes. -/
theorem plus_side_nodes (i : Fin 3) :
    movingNodes P u v (underToLaurent R) (laurentPlus_projection P c)
      (DoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i)) =
    BassOverlap.chartOverlapNodes P u v (underToLaurent R) (laurentPlus_projection P c)
      (DoubleSquareMergedSimplex.firstFace.toOrderHom (leftIndex i)) :=
  prePost_families_match (BassOverlap.commonReference P u v)
    (BassOverlap.projectionMap P (a := a)) (normalizedMap (laurentPlus P c))
    (sideBinarySource P u v) (sideBinaryNodes P u v)
    (moving_side_row P u v (underToLaurent R) (laurentPlus_projection P c))
    (old_side_row P u v (underToLaurent R) (laurentPlus_projection P c))
    0 (plus_side_corner P u v) i

/-- All inverse side nodes retain their distinct full original chart and reference data. -/
theorem minus_side_nodes (i : Fin 3) :
    movingNodes P u v (underToLaurentInvert R) (laurentMinus_projection P c)
      (DoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i)) =
    BassOverlap.chartOverlapNodes P u v (underToLaurentInvert R) (laurentMinus_projection P c)
      (DoubleSquareMergedSimplex.firstFace.toOrderHom (leftIndex i)) :=
  prePost_families_match (BassOverlap.commonReference P u v)
    (BassOverlap.projectionMap P (a := a)) (normalizedMap (laurentMinus P c))
    (sideBinarySource P u v) (sideBinaryNodes P u v)
    (moving_side_row P u v (underToLaurentInvert R) (laurentMinus_projection P c))
    (old_side_row P u v (underToLaurentInvert R) (laurentMinus_projection P c))
    0 (minus_side_corner P u v) i

end Quillen.PerfectComplexes.BassMOuterJoin
