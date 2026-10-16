/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Aglib.AlgebraicGeometry.BaseChange.Coefficients.Naturality
public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1BottomJoinFace

/-! The actual middle-triple right source, including its shared-node and association transports. -/
@[expose] public section

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
namespace Quillen.PerfectComplexes.BassH1Join
open BassReferenceMerge
section Schemes
variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)
  (r : C ⟶ A) (hr : q ≫ p = r)

include hq hr in
/-- The actual square and projection equations give the middle-right normalized total. -/
theorem projection_middle_right_geom : c ≫ r = (q' ≫ b) ≫ p :=
  (projection_middle_geom p q q' b c hq r hr).trans (Category.assoc q' b p).symm

include hq hr in
theorem projection_middle_right_source_eq : (ProjectionReference.reference c r).functor =
    (BinaryNormalizationSimplex.sourceMap (q' ≫ b) p).functor :=
  congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
    (congrArg boundedFlatNormalizedPullback (projection_middle_right_geom p q q' b c hq r hr))

/-- The shared original node is exactly its middle-triple normalized factorization. -/
theorem projection_middle_right_normal :
    ProjectionReference.nodes p q p' q' a b c hp hq r hr 9 =
    (⟨BinaryNormalizationSimplex.targetMap (q' ≫ b) p,
      eqToIso (projection_middle_right_source_eq p q q' b c hq r hr) ≪≫
        BinaryNormalizationSimplex.total (q' ≫ b) p⟩ : ProjectionReference.Node c r) := by
  have hn := native_middle_nodes p q p' q' a b c hp hq r hr 5
  refine hn.trans ?_
  have hf : (SplitTripleSimplex.vertices q' b p 5).functor =
      (BinaryNormalizationSimplex.targetMap (q' ≫ b) p).functor := rfl
  apply Sigma.ext (Model.Hom.ext hf)
  apply heq_of_eq
  change (eqToIso (ProjectionReference.anchor p q c r hr) ≪≫
      smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
        (DoubleSquareTrack.middle_eq p q q' b c hq).symm))) ≪≫
    smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (Category.assoc q' b p).symm) ≪≫
      boundedFlatNormalizedPullbackCompIso (q' ≫ b) p) = _
  rw [smallIso_trans, smallIso_eqToIso, smallIso_eqToIso,
    ← Iso.trans_assoc, eqToIso_trans, eqToIso_trans]
  rfl
end Schemes

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (u : a ⟶ b)
variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)

/--
The chart projection equality with the chart map and polynomial coefficient map composed before
polynomial projection.
-/
abbrev chartMiddleRightGeom := projection_middle_right_geom
  (polynomialProjection P a) (coefficientMap P (α.app a)) (coefficientMap P (α.app b))
  (coefficientMap P ((polynomialUnderFunctor R).map u))
  (coefficientMap P ((laurentUnderFunctor R).map u))
  (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P α u)
    (laurentProjection P a) ha

/--
The source-functor equality for the middle-right chart node, with the first two geometric maps
composed before normalization.
-/
abbrev chartMiddleRightSourceEq := projection_middle_right_source_eq
  (polynomialProjection P a) (coefficientMap P (α.app a)) (coefficientMap P (α.app b))
  (coefficientMap P ((polynomialUnderFunctor R).map u))
  (coefficientMap P ((laurentUnderFunctor R).map u))
  (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P α u)
    (laurentProjection P a) ha

/-- The original coefficient node retains the full actual middle-square reference route. -/
theorem chart_middle_right_normal : BassH0Diagram.chartNodes P u α ha 9 =
    (⟨BinaryNormalizationSimplex.targetMap
      (coefficientMap P (α.app b) ≫ coefficientMap P ((polynomialUnderFunctor R).map u))
      (polynomialProjection P a),
      eqToIso (chartMiddleRightSourceEq P u α ha) ≪≫ BinaryNormalizationSimplex.total
        (coefficientMap P (α.app b) ≫ coefficientMap P ((polynomialUnderFunctor R).map u))
        (polynomialProjection P a)⟩ : BassH0Diagram.Node P u) :=
  projection_middle_right_normal (polynomialProjection P a) (coefficientMap P (α.app a))
    (polynomialProjection P b) (coefficientMap P (α.app b)) (coefficientMap P u)
    (coefficientMap P ((polynomialUnderFunctor R).map u))
    (coefficientMap P ((laurentUnderFunctor R).map u))
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
      (polynomialUnderCoefficient R) u)
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P α u)
      (laurentProjection P a) ha

end Quillen.PerfectComplexes.BassH1Join
