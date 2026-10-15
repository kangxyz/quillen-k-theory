/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MReferenceRows

/-! Actual polynomial centre references on both M-source/H0-target chart pieces. -/
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
open BassReferenceMerge BassH0Merge BassH1Join BassMComponents BassMReferences
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)
variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)
  (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)

/-- The direct original polynomial square has exactly the moving diagram's geometric total. -/
theorem direct_polynomial_total :
    coefficientMap P ((polynomialUnderFunctor R).map (u ≫ v)) ≫ polynomialProjection P a =
      polynomialProjection P c ≫ coefficientMap P v ≫ coefficientMap P u := by
  have hn := coefficientTransformation_naturality P (polynomialUnderCoefficient R) (u ≫ v)
  change coefficientMap P ((polynomialUnderFunctor R).map (u ≫ v)) ≫ polynomialProjection P a =
    polynomialProjection P c ≫ coefficientMap P (u ≫ v) at hn
  rw [coefficientMap_comp] at hn
  exact hn

include hc in
/-- The unchanged moving source reference as the actual binary chart/total factorization. -/
theorem movingReferenceEq : (BassOverlap.commonReference P u v).functor =
    (BinaryNormalizationSimplex.sourceMap (coefficientMap P (α.app c))
      (polynomialProjection P c ≫ coefficientMap P v ≫ coefficientMap P u)).functor :=
  congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
    (congrArg boundedFlatNormalizedPullback (moving_total P u v α hc).symm)

include ha in
/-- The original H0 polynomial centre retains its full original source equality. -/
theorem oldPolynomialReference : (BassOverlap.commonReference P u v).functor =
    (BinaryNormalizationSimplex.sourceMap (coefficientMap P (α.app c))
      (coefficientMap P ((polynomialUnderFunctor R).map (u ≫ v)) ≫
        polynomialProjection P a)).functor :=
  (reference_eq P u v).trans (chartMiddleSourceEq P (u ≫ v) α ha)

/-- The original moving centre retains its actual normalized chart/total reference. -/
theorem moving_center_canonical : movingNodes P u v α hc 0 =
    binaryTargetNode (BassOverlap.commonReference P u v) (coefficientMap P (α.app c))
      (polynomialProjection P c ≫ coefficientMap P v ≫ coefficientMap P u)
      (movingReferenceEq P u v α hc) := by
  have hf : (movingNodes P u v α hc 0).1.functor =
      (BinaryNormalizationSimplex.targetMap (coefficientMap P (α.app c))
        (polynomialProjection P c ≫ coefficientMap P v ≫ coefficientMap P u)).functor := rfl
  apply Sigma.ext (Model.Hom.ext hf)
  apply heq_of_eq
  change movingIso P u v α hc ≪≫
    isoWhiskerRight (Iso.refl (polynomialSource P u v).functor)
      (normalizedMap (coefficientMap P (α.app c))).functor =
    eqToIso (movingReferenceEq P u v α hc) ≪≫ BinaryNormalizationSimplex.total
      (coefficientMap P (α.app c))
      (polynomialProjection P c ≫ coefficientMap P v ≫ coefficientMap P u)
  rw [isoWhiskerRight_refl]
  refine (Iso.trans_refl (movingIso P u v α hc)).trans ?_
  change smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
      (moving_total P u v α hc).symm) ≪≫
      boundedFlatNormalizedPullbackCompIso (coefficientMap P (α.app c))
        (polynomialProjection P c ≫ coefficientMap P v ≫ coefficientMap P u)) = _
  rw [smallIso_trans, smallIso_eqToIso]
  rfl

/-- The H0 polynomial centre retains the identical kind of actual binary factorization node. -/
theorem old_polynomial_center_canonical :
    anchorNode (F₀ := BassOverlap.commonReference P u v)
      (F₁ := BassH0Diagram.reference P (u ≫ v)) (eqToIso (reference_eq P u v))
      (BassH0Diagram.chartNodes P (u ≫ v) α ha 5) =
    binaryTargetNode (BassOverlap.commonReference P u v) (coefficientMap P (α.app c))
      (coefficientMap P ((polynomialUnderFunctor R).map (u ≫ v)) ≫ polynomialProjection P a)
      (oldPolynomialReference P u v α ha) := by
  have hn := congrArg (anchorNode (F₀ := BassOverlap.commonReference P u v)
    (F₁ := BassH0Diagram.reference P (u ≫ v)) (eqToIso (reference_eq P u v)))
      (chart_middle_normal P (u ≫ v) α ha)
  exact hn.trans (anchor_binary_target_node (BassOverlap.commonReference P u v)
    (BassH0Diagram.reference P (u ≫ v)) (coefficientMap P (α.app c))
    (coefficientMap P ((polynomialUnderFunctor R).map (u ≫ v)) ≫ polynomialProjection P a)
    (reference_eq P u v) (chartMiddleSourceEq P (u ≫ v) α ha))

/-- The full polynomial centre nodes agree by original naturality and composition. -/
theorem source_polynomial_center : movingNodes P u v α hc 0 =
    anchorNode (F₀ := BassOverlap.commonReference P u v)
      (F₁ := BassH0Diagram.reference P (u ≫ v)) (eqToIso (reference_eq P u v))
      (BassH0Diagram.chartNodes P (u ≫ v) α ha 5) := by
  rw [moving_center_canonical, old_polynomial_center_canonical]
  exact binaryTargetNode_congr _ rfl (direct_polynomial_total P u v).symm _ _

end Quillen.PerfectComplexes.BassMOuterJoin
