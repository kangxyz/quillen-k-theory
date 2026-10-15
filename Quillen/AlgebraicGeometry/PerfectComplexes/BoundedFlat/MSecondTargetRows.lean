/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Coefficients.Naturality
public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MFirstTargetNodes

/-! Actual full row forms for the second and fourth native reassociation paths. -/
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
variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (hb : coefficientMap P (α.app b) ≫ polynomialProjection P b = laurentProjection P b)
  (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)

/--
The H1 middle-chart nodes, precomposed with the normalized coefficient map of `u` and referenced
to the common overlap.
-/
abbrev h1MiddleChartNodes (i : Fin 18) :=
  preReferenceNode (BassOverlap.commonReference P u v) (normalizedMap (coefficientMap P u))
    (BassH1References.middleIso P u v) (BassH0Diagram.chartNodes P v α hb i)

/--
The right-row reference for the polynomial `v`-map followed by projection, with the normalized
`u`-map on the left.
-/
abbrev movingQFirstBaseIso := rightRowReference (polynomialSource P u v)
  (coefficientMap P ((polynomialUnderFunctor R).map v)) (polynomialProjection P b)
  (coefficientMap P u) (polynomialMiddleIso P u v)
/--
The right-row reference for projection followed by the coefficient map of `v`, with the
normalized `u`-map on the left.
-/
abbrev movingQSecondBaseIso := rightRowReference (polynomialSource P u v)
  (polynomialProjection P c) (coefficientMap P v) (coefficientMap P u) (Iso.refl _)

/--
The first moving `v`-square row reference, obtained by postcomposing its polynomial reference
with the target chart map.
-/
def movingQFirstIso := movingIso P u v α hc ≪≫ isoWhiskerRight (movingQFirstBaseIso P u v)
  (normalizedMap (coefficientMap P (α.app c))).functor
/--
The second moving `v`-square row reference, obtained by postcomposing its polynomial reference
with the target chart map.
-/
def movingQSecondIso := movingIso P u v α hc ≪≫ isoWhiskerRight (movingQSecondBaseIso P u v)
  (normalizedMap (coefficientMap P (α.app c))).functor

/--
The original H1 first `v`-square row reference, combining its middle-chart reference with binary
total normalization.
-/
def oldQFirstIso := BassH1References.middleIso P u v ≪≫
  isoWhiskerLeft (normalizedMap (coefficientMap P u)).functor
    (polynomialMiddleReference P v α hb ≪≫ BinaryNormalizationSimplex.total
      (coefficientMap P (α.app c))
      (coefficientMap P ((polynomialUnderFunctor R).map v) ≫ polynomialProjection P b))
/--
The original H1 second `v`-square row reference, combining its last-triple reference with binary
total normalization.
-/
def oldQSecondIso := BassH1References.middleIso P u v ≪≫
  isoWhiskerLeft (normalizedMap (coefficientMap P u)).functor
    (BassH1H0Boundary.lastReference P v α hb ≪≫ BinaryNormalizationSimplex.total
      (coefficientMap P (α.app c)) (polynomialProjection P c ≫ coefficientMap P v))

/-- The first original v-square row is retained between the original u map and chart map. -/
theorem moving_q_first_row (i : Fin 3) :
    movingNodes P u v α hc (DoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i)) =
    prePostNodes (BassOverlap.commonReference P u v) (normalizedMap (coefficientMap P u))
      (normalizedMap (coefficientMap P (α.app c)))
      (BinaryNormalizationSimplex.sourceMap
        (coefficientMap P ((polynomialUnderFunctor R).map v)) (polynomialProjection P b))
      (binaryNodes (coefficientMap P ((polynomialUnderFunctor R).map v)) (polynomialProjection P b))
      (movingQFirstIso P u v α hc) i := by
  have hn := congrArg (postReferenceNode (BassOverlap.commonReference P u v)
    (normalizedMap (coefficientMap P (α.app c))) (movingIso P u v α hc))
    (rectangle_middle_right_nodes (coefficientMap P u) (coefficientMap P v)
      (coefficientMap P ((polynomialUnderFunctor R).map u))
      (coefficientMap P ((polynomialUnderFunctor R).map v))
      (polynomialProjection P a) (polynomialProjection P b) (polynomialProjection P c)
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
        (polynomialUnderCoefficient R) u).symm
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
        (polynomialUnderCoefficient R) v).symm i)
  exact hn.trans (post_pre_node (BassOverlap.commonReference P u v)
    (normalizedMap (coefficientMap P u)) (normalizedMap (coefficientMap P (α.app c)))
    (BinaryNormalizationSimplex.sourceMap
      (coefficientMap P ((polynomialUnderFunctor R).map v)) (polynomialProjection P b))
    (binaryNodes (coefficientMap P ((polynomialUnderFunctor R).map v)) (polynomialProjection P b))
    (movingQFirstBaseIso P u v) (movingIso P u v α hc) i)

/-- The second original v-square row retains its native first-triple composition reference. -/
theorem moving_q_second_row (i : Fin 3) :
    movingNodes P u v α hc (DoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i)) =
    prePostNodes (BassOverlap.commonReference P u v) (normalizedMap (coefficientMap P u))
      (normalizedMap (coefficientMap P (α.app c)))
      (BinaryNormalizationSimplex.sourceMap (polynomialProjection P c) (coefficientMap P v))
      (binaryNodes (polynomialProjection P c) (coefficientMap P v))
      (movingQSecondIso P u v α hc) i :=
  (congrArg (postReferenceNode (BassOverlap.commonReference P u v)
    (normalizedMap (coefficientMap P (α.app c))) (movingIso P u v α hc))
    (rectangle_first_right_nodes (coefficientMap P u) (coefficientMap P v)
      (coefficientMap P ((polynomialUnderFunctor R).map u))
      (coefficientMap P ((polynomialUnderFunctor R).map v))
      (polynomialProjection P a) (polynomialProjection P b) (polynomialProjection P c)
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
        (polynomialUnderCoefficient R) u).symm
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
        (polynomialUnderCoefficient R) v).symm i)).trans
    (post_pre_node (BassOverlap.commonReference P u v)
      (normalizedMap (coefficientMap P u)) (normalizedMap (coefficientMap P (α.app c)))
      (BinaryNormalizationSimplex.sourceMap (polynomialProjection P c) (coefficientMap P v))
      (binaryNodes (polynomialProjection P c) (coefficientMap P v))
      (movingQSecondBaseIso P u v) (movingIso P u v α hc) i)

/-- H1's corresponding first row uses the same native v-square under its literal fixed maps. -/
theorem old_q_first_row (i : Fin 3) :
    h1MiddleChartNodes P u v α hb
      (DoubleSquareMergedSimplex.middleFace.toOrderHom (leftIndex i)) =
    prePostNodes (BassOverlap.commonReference P u v) (normalizedMap (coefficientMap P u))
      (normalizedMap (coefficientMap P (α.app c)))
      (BinaryNormalizationSimplex.sourceMap
        (coefficientMap P ((polynomialUnderFunctor R).map v)) (polynomialProjection P b))
      (binaryNodes (coefficientMap P ((polynomialUnderFunctor R).map v)) (polynomialProjection P b))
      (oldQFirstIso P u v α hb) i := by
  have hn := congrArg (preReferenceNode (BassOverlap.commonReference P u v)
    (normalizedMap (coefficientMap P u)) (BassH1References.middleIso P u v))
    (native_middle_column (polynomialProjection P b) (coefficientMap P (α.app b))
      (polynomialProjection P c) (coefficientMap P (α.app c)) (coefficientMap P v)
      (coefficientMap P ((polynomialUnderFunctor R).map v))
      (coefficientMap P ((laurentUnderFunctor R).map v))
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
        (polynomialUnderCoefficient R) v)
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P α v)
        (laurentProjection P b) hb i)
  exact hn.trans (pre_post_node (BassOverlap.commonReference P u v)
    (normalizedMap (coefficientMap P u)) (normalizedMap (coefficientMap P (α.app c)))
    (CoefficientSquareFamilies.polynomialSource P v)
    (binaryNodes (coefficientMap P ((polynomialUnderFunctor R).map v)) (polynomialProjection P b))
    _ (BassH1References.middleIso P u v) i)

/-- H1's second row retains the same original last-triple normalization and source transport. -/
theorem old_q_second_row (i : Fin 3) :
    h1MiddleChartNodes P u v α hb
      (DoubleSquareMergedSimplex.lastFace.toOrderHom (leftIndex i)) =
    prePostNodes (BassOverlap.commonReference P u v) (normalizedMap (coefficientMap P u))
      (normalizedMap (coefficientMap P (α.app c)))
      (BinaryNormalizationSimplex.sourceMap (polynomialProjection P c) (coefficientMap P v))
      (binaryNodes (polynomialProjection P c) (coefficientMap P v))
      (oldQSecondIso P u v α hb) i := by
  have hn := congrArg (preReferenceNode (BassOverlap.commonReference P u v)
    (normalizedMap (coefficientMap P u)) (BassH1References.middleIso P u v))
    (native_last_column (polynomialProjection P b) (coefficientMap P (α.app b))
      (polynomialProjection P c) (coefficientMap P (α.app c)) (coefficientMap P v)
      (coefficientMap P ((polynomialUnderFunctor R).map v))
      (coefficientMap P ((laurentUnderFunctor R).map v))
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
        (polynomialUnderCoefficient R) v)
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P α v)
        (laurentProjection P b) hb i)
  exact hn.trans (pre_post_node (BassOverlap.commonReference P u v)
    (normalizedMap (coefficientMap P u)) (normalizedMap (coefficientMap P (α.app c)))
    (BinaryNormalizationSimplex.sourceMap (polynomialProjection P c) (coefficientMap P v))
    (binaryNodes (polynomialProjection P c) (coefficientMap P v))
    _ (BassH1References.middleIso P u v) i)

end Quillen.PerfectComplexes.BassMOuterJoin
