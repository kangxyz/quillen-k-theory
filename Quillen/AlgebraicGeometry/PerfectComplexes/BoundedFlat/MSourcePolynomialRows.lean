/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MSourcePolynomialCenter
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MPolynomialOuterRows

/-! Every full polynomial-path node on the M-source/H0-target boundary. -/
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
  (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)
  (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)

abbrev polynomialTotalEq := targetTotalSourceEq
  (coefficientMap P u) (coefficientMap P v)
  (coefficientMap P ((polynomialUnderFunctor R).map u))
  (coefficientMap P ((polynomialUnderFunctor R).map v))
  (polynomialProjection P a) (polynomialProjection P b) (polynomialProjection P c)
  (coefficientTransformation_naturality P (polynomialUnderCoefficient R) u).symm
  (coefficientTransformation_naturality P (polynomialUnderCoefficient R) v).symm

def movingTargetRowIso := movingIso P u v α hc ≪≫
  isoWhiskerRight (eqToIso (polynomialTotalEq P u v))
    (normalizedMap (coefficientMap P (α.app c))).functor

def oldFirstPolynomialRowIso := eqToIso (reference_eq P u v) ≪≫
  (polynomialMiddleReference P (u ≫ v) α ha ≪≫ BinaryNormalizationSimplex.total
    (coefficientMap P (α.app c))
    (coefficientMap P ((polynomialUnderFunctor R).map (u ≫ v)) ≫ polynomialProjection P a))

def oldSecondPolynomialRowIso := eqToIso (reference_eq P u v) ≪≫
  (BassH1H0Boundary.lastReference P (u ≫ v) α ha ≪≫ BinaryNormalizationSimplex.total
    (coefficientMap P (α.app c)) (polynomialProjection P c ≫ coefficientMap P (u ≫ v)))

/-- The moving target-total row retains its full source transport before chart mapping. -/
theorem moving_target_total_row (i : Fin 3) :
    movingNodes P u v α hc (targetTotalIndex i) =
    postReferenceNode (BassOverlap.commonReference P u v)
      (normalizedMap (coefficientMap P (α.app c))) (movingTargetRowIso P u v α hc)
      (binaryNodes (coefficientMap P ((polynomialUnderFunctor R).map v) ≫
        coefficientMap P ((polynomialUnderFunctor R).map u)) (polynomialProjection P a) i) := by
  have hn := congrArg (postReferenceNode (BassOverlap.commonReference P u v)
    (normalizedMap (coefficientMap P (α.app c))) (movingIso P u v α hc))
      (rectangle_target_total_nodes (coefficientMap P u) (coefficientMap P v)
        (coefficientMap P ((polynomialUnderFunctor R).map u))
        (coefficientMap P ((polynomialUnderFunctor R).map v))
        (polynomialProjection P a) (polynomialProjection P b) (polynomialProjection P c)
        (coefficientTransformation_naturality P (polynomialUnderCoefficient R) u).symm
        (coefficientTransformation_naturality P (polynomialUnderCoefficient R) v).symm i)
  exact hn.trans (post_anchor_node (BassOverlap.commonReference P u v)
    (normalizedMap (coefficientMap P (α.app c))) (movingIso P u v α hc)
    (eqToIso (polynomialTotalEq P u v)) _)

/-- The other original moving row is the unchanged projection/coefficient binary family. -/
theorem moving_source_total_row (i : Fin 3) :
    movingNodes P u v α hc (sourceTotalIndex i) =
    postReferenceNode (BassOverlap.commonReference P u v)
      (normalizedMap (coefficientMap P (α.app c))) (movingIso P u v α hc)
      (binaryNodes (polynomialProjection P c) (coefficientMap P v ≫ coefficientMap P u) i) :=
  congrArg (postReferenceNode (BassOverlap.commonReference P u v)
    (normalizedMap (coefficientMap P (α.app c))) (movingIso P u v α hc))
    (rectangle_source_total_nodes (coefficientMap P u) (coefficientMap P v)
      (coefficientMap P ((polynomialUnderFunctor R).map u))
      (coefficientMap P ((polynomialUnderFunctor R).map v))
      (polynomialProjection P a) (polynomialProjection P b) (polynomialProjection P c)
      (coefficientTransformation_naturality P (polynomialUnderCoefficient R) u).symm
      (coefficientTransformation_naturality P (polynomialUnderCoefficient R) v).symm i)

/-- The original H0 first polynomial row retains its actual middle-triple source normalization. -/
theorem old_first_polynomial_row (i : Fin 3) :
    anchorNode (F₀ := BassOverlap.commonReference P u v)
      (F₁ := BassH0Diagram.reference P (u ≫ v)) (eqToIso (reference_eq P u v))
      (BassH0Diagram.chartNodes P (u ≫ v) α ha
        (DoubleSquareMergedSimplex.middleFace.toOrderHom (leftIndex i))) =
    postReferenceNode (BassOverlap.commonReference P u v)
      (normalizedMap (coefficientMap P (α.app c))) (oldFirstPolynomialRowIso P u v α ha)
      (binaryNodes (coefficientMap P ((polynomialUnderFunctor R).map (u ≫ v)))
        (polynomialProjection P a) i) := by
  have hn := congrArg (anchorNode (F₀ := BassOverlap.commonReference P u v)
    (F₁ := BassH0Diagram.reference P (u ≫ v)) (eqToIso (reference_eq P u v)))
    (native_middle_column (polynomialProjection P a) (coefficientMap P (α.app a))
      (polynomialProjection P c) (coefficientMap P (α.app c)) (coefficientMap P (u ≫ v))
      (coefficientMap P ((polynomialUnderFunctor R).map (u ≫ v)))
      (coefficientMap P ((laurentUnderFunctor R).map (u ≫ v)))
      (coefficientTransformation_naturality P (polynomialUnderCoefficient R) (u ≫ v))
      (coefficientTransformation_naturality P α (u ≫ v)) (laurentProjection P a) ha i)
  exact hn.trans (anchor_post_node (normalizedMap (coefficientMap P (α.app c)))
    (eqToIso (reference_eq P u v)) _ _)

/-- H0's second polynomial row retains the original last-triple geometric equality transport. -/
theorem old_second_polynomial_row (i : Fin 3) :
    anchorNode (F₀ := BassOverlap.commonReference P u v)
      (F₁ := BassH0Diagram.reference P (u ≫ v)) (eqToIso (reference_eq P u v))
      (BassH0Diagram.chartNodes P (u ≫ v) α ha
        (DoubleSquareMergedSimplex.lastFace.toOrderHom (leftIndex i))) =
    postReferenceNode (BassOverlap.commonReference P u v)
      (normalizedMap (coefficientMap P (α.app c))) (oldSecondPolynomialRowIso P u v α ha)
      (binaryNodes (polynomialProjection P c) (coefficientMap P (u ≫ v)) i) := by
  have hn := congrArg (anchorNode (F₀ := BassOverlap.commonReference P u v)
    (F₁ := BassH0Diagram.reference P (u ≫ v)) (eqToIso (reference_eq P u v)))
    (native_last_column (polynomialProjection P a) (coefficientMap P (α.app a))
      (polynomialProjection P c) (coefficientMap P (α.app c)) (coefficientMap P (u ≫ v))
      (coefficientMap P ((polynomialUnderFunctor R).map (u ≫ v)))
      (coefficientMap P ((laurentUnderFunctor R).map (u ≫ v)))
      (coefficientTransformation_naturality P (polynomialUnderCoefficient R) (u ≫ v))
      (coefficientTransformation_naturality P α (u ≫ v)) (laurentProjection P a) ha i)
  exact hn.trans (anchor_post_node (normalizedMap (coefficientMap P (α.app c)))
    (eqToIso (reference_eq P u v)) _ _)

/-- Every complete first binary row node is shared with the original H0 polynomial target. -/
theorem source_polynomial_first_nodes (i : Fin 3) :
    movingNodes P u v α hc (targetTotalIndex i) =
    anchorNode (F₀ := BassOverlap.commonReference P u v)
      (F₁ := BassH0Diagram.reference P (u ≫ v)) (eqToIso (reference_eq P u v))
      (BassH0Diagram.chartNodes P (u ≫ v) α ha
        (DoubleSquareMergedSimplex.middleFace.toOrderHom (leftIndex i))) :=
  post_binary_families_match (BassOverlap.commonReference P u v)
    (normalizedMap (coefficientMap P (α.app c)))
    (coefficientMap P ((polynomialUnderFunctor R).map v) ≫
      coefficientMap P ((polynomialUnderFunctor R).map u)) (polynomialProjection P a)
    (polynomial_composite P u v).symm rfl
    (moving_target_total_row P u v α hc) (old_first_polynomial_row P u v α ha)
    (source_polynomial_center P u v α ha hc) i

/-- Every second-row node retains its actual reference and coefficient transport. -/
theorem source_polynomial_second_nodes (i : Fin 3) :
    movingNodes P u v α hc (sourceTotalIndex i) =
    anchorNode (F₀ := BassOverlap.commonReference P u v)
      (F₁ := BassH0Diagram.reference P (u ≫ v)) (eqToIso (reference_eq P u v))
      (BassH0Diagram.chartNodes P (u ≫ v) α ha
        (DoubleSquareMergedSimplex.lastFace.toOrderHom (leftIndex i))) :=
  post_binary_families_match (BassOverlap.commonReference P u v)
    (normalizedMap (coefficientMap P (α.app c)))
    (polynomialProjection P c) (coefficientMap P v ≫ coefficientMap P u)
    rfl (coefficientMap_comp P u v).symm
    (moving_source_total_row P u v α hc) (old_second_polynomial_row P u v α ha)
    (source_polynomial_center P u v α ha hc) i

/-- These labels are the literal two-binary word of the entire original moving source path. -/
def movingSourceWordIndex : Fin 5 → Fin 18 := ![0, 14, 15, 1, 2]

/-- The full five-node source path agrees, including both raw normalization intermediates. -/
theorem source_polynomial_word_nodes (i : Fin 5) :
    movingNodes P u v α hc (movingSourceWordIndex i) =
    anchorNode (F₀ := BassOverlap.commonReference P u v)
      (F₁ := BassH0Diagram.reference P (u ≫ v)) (eqToIso (reference_eq P u v))
      (BassH0Diagram.chartNodes P (u ≫ v) α ha (polynomialWordIndex i)) := by
  fin_cases i
  · exact source_polynomial_center P u v α ha hc
  · exact source_polynomial_first_nodes P u v α ha hc 1
  · exact source_polynomial_first_nodes P u v α ha hc 2
  · exact source_polynomial_second_nodes P u v α ha hc 1
  · exact source_polynomial_second_nodes P u v α ha hc 2

end Quillen.PerfectComplexes.BassMOuterJoin
