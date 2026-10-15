/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ProjectionMiddleNormalNode
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ProductReferenceRows

/-! Full central reference equality for the first/product-column H1 joins. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.PolynomialBaseChange AlgebraicGeometry.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassH1Join
open BassReferenceMerge BassH1References
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)
variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)
  (hb : coefficientMap P (α.app b) ≫ polynomialProjection P b = laurentProjection P b)

abbrev chartMiddleGeom := projection_middle_geom
  (polynomialProjection P a) (coefficientMap P (α.app a)) (coefficientMap P (α.app b))
  (coefficientMap P ((polynomialUnderFunctor R).map u))
  (coefficientMap P ((laurentUnderFunctor R).map u))
  (coefficientTransformation_naturality P α u) (laurentProjection P a) ha

def firstPolynomialCenter : BassOverlap.Node P u v :=
  postReferenceNode (BassOverlap.commonReference P u v) (BassH1Components.laurentMap P v)
    (firstIso P u v)
    (⟨BinaryNormalizationSimplex.targetMap (coefficientMap P (α.app b))
      (coefficientMap P ((polynomialUnderFunctor R).map u) ≫ polynomialProjection P a),
      eqToIso (chartMiddleSourceEq P u α ha) ≪≫ BinaryNormalizationSimplex.total
        (coefficientMap P (α.app b))
        (coefficientMap P ((polynomialUnderFunctor R).map u) ≫ polynomialProjection P a)⟩ :
      BassH0Diagram.Node P u)

def productPolynomialCenter : BassOverlap.Node P u v :=
  BassH0Merge.preReferenceNode (BassOverlap.commonReference P u v)
    (CoefficientSquareFamilies.polynomialSource P u) (chartIso P u v α hb)
    (⟨BinaryNormalizationSimplex.targetMap
      (coefficientMap P ((laurentUnderFunctor R).map v)) (coefficientMap P (α.app b)),
      BinaryNormalizationSimplex.total
        (coefficientMap P ((laurentUnderFunctor R).map v)) (coefficientMap P (α.app b))⟩ :
      NativeSquareFiveSimplex.Node
        (coefficientMap P ((laurentUnderFunctor R).map v)) (coefficientMap P (α.app b)))

theorem first_polynomial_center_original :
    postReferenceNode (BassOverlap.commonReference P u v) (BassH1Components.laurentMap P v)
      (firstIso P u v) (BassH0Diagram.chartNodes P u α ha 5) =
      firstPolynomialCenter P u v α ha :=
  congrArg (postReferenceNode (BassOverlap.commonReference P u v)
    (BassH1Components.laurentMap P v) (firstIso P u v)) (chart_middle_normal P u α ha)

/-- The product's original source/normalized vertex has this exact complete reference. -/
theorem product_polynomial_center_original :
    BassH1References.chartNodes P u v α hb 2 = productPolynomialCenter P u v α hb := by
  change BassH1References.chartNodes P u v α hb (Quillen.SimplexGrid.index 4 4 (0, 2)) = _
  unfold BassH1References.chartNodes CommonReferenceProduct.vertices
    CommonReferenceProduct.references
  rw [Quillen.SimplexGrid.decode_index]
  dsimp only
  have hf : (CoefficientSquareFamilies.polynomialSource P u ≫
      BinaryNormalizationSimplex.targetMap
        (coefficientMap P ((laurentUnderFunctor R).map v)) (coefficientMap P (α.app b))).functor =
      (productPolynomialCenter P u v α hb).1.functor := rfl
  apply Sigma.ext (Model.Hom.ext hf)
  apply heq_of_eq
  change chartIso P u v α hb ≪≫
    (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
      ((Iso.refl (CoefficientSquareFamilies.polynomialSource P u).functor).prod
        (BinaryNormalizationSimplex.total
          (coefficientMap P ((laurentUnderFunctor R).map v)) (coefficientMap P (α.app b)))) =
    chartIso P u v α hb ≪≫
      isoWhiskerLeft (CoefficientSquareFamilies.polynomialSource P u).functor
        (BinaryNormalizationSimplex.total
          (coefficientMap P ((laurentUnderFunctor R).map v)) (coefficientMap P (α.app b)))
  have hi := composition_pair_iso
    (Iso.refl (CoefficientSquareFamilies.polynomialSource P u).functor)
    (BinaryNormalizationSimplex.total
      (coefficientMap P ((laurentUnderFunctor R).map v)) (coefficientMap P (α.app b)))
  simp only [isoWhiskerRight_refl, Iso.refl_trans] at hi
  exact congrArg (fun ν ↦ chartIso P u v α hb ≪≫ ν) hi

theorem polynomial_center_functor : (firstPolynomialCenter P u v α ha).1.functor =
    (productPolynomialCenter P u v α hb).1.functor := rfl

/-- The actual product and postcomposition routes agree by the original three-factor coherence. -/
theorem polynomial_center_reference : (firstPolynomialCenter P u v α ha).2 =
    (productPolynomialCenter P u v α hb).2 := by
  have he : eqToIso (chartMiddleSourceEq P u α ha) ≪≫ BinaryNormalizationSimplex.total
      (coefficientMap P (α.app b))
      (coefficientMap P ((polynomialUnderFunctor R).map u) ≫ polynomialProjection P a) =
    smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (chartMiddleGeom P u α ha)) ≪≫
      boundedFlatNormalizedPullbackCompIso (coefficientMap P (α.app b))
        (coefficientMap P ((polynomialUnderFunctor R).map u) ≫ polynomialProjection P a)) := by
    rw [smallIso_trans, smallIso_eqToIso]
    rfl
  change firstIso P u v ≪≫ isoWhiskerRight
      (eqToIso (chartMiddleSourceEq P u α ha) ≪≫ BinaryNormalizationSimplex.total
        (coefficientMap P (α.app b))
        (coefficientMap P ((polynomialUnderFunctor R).map u) ≫ polynomialProjection P a))
      (BassH1Components.laurentMap P v).functor =
    chartIso P u v α hb ≪≫ isoWhiskerLeft (CoefficientSquareFamilies.polynomialSource P u).functor
      (BinaryNormalizationSimplex.total
        (coefficientMap P ((laurentUnderFunctor R).map v)) (coefficientMap P (α.app b)))
  rw [he]
  change smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (first_total P u v).symm) ≪≫
      boundedFlatNormalizedPullbackCompIso
        (coefficientMap P ((laurentUnderFunctor R).map v))
        (coefficientMap P ((laurentUnderFunctor R).map u) ≫ laurentProjection P a)) ≪≫
    isoWhiskerRight
      (smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (chartMiddleGeom P u α ha)) ≪≫
        boundedFlatNormalizedPullbackCompIso (coefficientMap P (α.app b))
          (coefficientMap P ((polynomialUnderFunctor R).map u) ≫ polynomialProjection P a)))
      (AsSmall.down ⋙ boundedFlatNormalizedPullback
        (coefficientMap P ((laurentUnderFunctor R).map v)) ⋙ AsSmall.up) =
    smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (chart_total P u v α hb).symm) ≪≫
      boundedFlatNormalizedPullbackCompIso
        (coefficientMap P ((laurentUnderFunctor R).map v) ≫ coefficientMap P (α.app b))
        (coefficientMap P ((polynomialUnderFunctor R).map u) ≫ polynomialProjection P a)) ≪≫
    isoWhiskerLeft (AsSmall.down ⋙ boundedFlatNormalizedPullback
      (coefficientMap P ((polynomialUnderFunctor R).map u) ≫ polynomialProjection P a) ⋙ AsSmall.up)
      (smallIso (boundedFlatNormalizedPullbackCompIso
        (coefficientMap P ((laurentUnderFunctor R).map v)) (coefficientMap P (α.app b))))
  rw [smallIso_postcomp, smallIso_precomp, ← smallIso_trans, ← smallIso_trans]
  apply congrArg smallIso
  simpa only [eqToIso_refl, Iso.refl_trans, Iso.trans_assoc] using
    (anchored_factorizations_strict
      (coefficientMap P ((laurentUnderFunctor R).map v)) (coefficientMap P (α.app b))
      (coefficientMap P ((polynomialUnderFunctor R).map u) ≫ polynomialProjection P a)
      (coefficientMap P ((laurentUnderFunctor R).map v) ≫ coefficientMap P (α.app b))
      (coefficientMap P ((laurentUnderFunctor R).map u) ≫ laurentProjection P a)
      (laurentProjection P c ≫ coefficientMap P v ≫ coefficientMap P u)
      rfl (chartMiddleGeom P u α ha) (chart_total P u v α hb).symm (first_total P u v).symm).symm

/-- The full original central nodes agree; no matching-functor quotient is taken. -/
theorem first_product_polynomial_center :
    postReferenceNode (BassOverlap.commonReference P u v) (BassH1Components.laurentMap P v)
      (firstIso P u v) (BassH0Diagram.chartNodes P u α ha 5) =
      BassH1References.chartNodes P u v α hb 2 := by
  rw [first_polynomial_center_original, product_polynomial_center_original]
  apply Sigma.ext (Model.Hom.ext (polynomial_center_functor P u v α ha hb))
  exact heq_of_eq (polynomial_center_reference P u v α ha hb)

/-- Actual positive first/product-column center, including its entire reference iso. -/
theorem plus_column_center : BassH1References.firstNodes P u v 5 =
    BassH1References.chartNodes P u v (underToLaurent R) (laurentPlus_projection P b) 2 :=
  first_product_polynomial_center P u v (underToLaurent R)
    (laurentPlus_projection P a) (laurentPlus_projection P b)

/-- The distinct inverse first/product-column center retains the original inverse projection. -/
theorem minus_column_center : BassH1References.firstNodes P u v 16 =
    BassH1References.chartNodes P u v (underToLaurentInvert R) (laurentMinus_projection P b) 2 :=
  first_product_polynomial_center P u v (underToLaurentInvert R)
    (laurentMinus_projection P a) (laurentMinus_projection P b)

end Quillen.PerfectComplexes.BassH1Join
