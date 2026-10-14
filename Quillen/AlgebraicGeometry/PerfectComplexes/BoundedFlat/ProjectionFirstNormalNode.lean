/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ProjectionPolynomialColumns

/-! The unchanged normalized first right-row node of an original projection rectangle. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.PolynomialBaseChange Quillen.Scheme.CoefficientBaseChange
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

include hr in
/-- The actual projection equation, with the original right association retained. -/
theorem projection_first_geom : c ≫ r = (c ≫ q) ≫ p := by
  rw [Category.assoc, hr]

include hr in
theorem projection_first_source_eq : (ProjectionReference.reference c r).functor =
    (BinaryNormalizationSimplex.sourceMap (c ≫ q) p).functor :=
  congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
    (congrArg boundedFlatNormalizedPullback (projection_first_geom p q c r hr))

theorem projection_first_normal_functor :
    (ProjectionReference.nodes p q p' q' a b c hp hq r hr 9).1.functor =
      (BinaryNormalizationSimplex.targetMap (c ≫ q) p).functor := rfl

/-- The first normalized right-row reference retains its native associativity transport. -/
theorem projection_first_normal_reference :
    (ProjectionReference.nodes p q p' q' a b c hp hq r hr 9).2 =
      eqToIso (projection_first_source_eq p q c r hr) ≪≫
        BinaryNormalizationSimplex.total (c ≫ q) p := by
  change eqToIso (ProjectionReference.anchor p q c r hr) ≪≫
    smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (Category.assoc c q p).symm) ≪≫
      boundedFlatNormalizedPullbackCompIso (c ≫ q) p) = _
  rw [smallIso_trans, smallIso_eqToIso, ← Iso.trans_assoc, eqToIso_trans]
  rfl

/-- Full original normalized right-row node, including the actual dependent reference. -/
theorem projection_first_normal :
    ProjectionReference.nodes p q p' q' a b c hp hq r hr 9 =
      (⟨BinaryNormalizationSimplex.targetMap (c ≫ q) p,
        eqToIso (projection_first_source_eq p q c r hr) ≪≫
          BinaryNormalizationSimplex.total (c ≫ q) p⟩ : ProjectionReference.Node c r) := by
  apply Sigma.ext (Model.Hom.ext
    (projection_first_normal_functor p q p' q' a b c hp hq r hr))
  exact heq_of_eq (projection_first_normal_reference p q p' q' a b c hp hq r hr)
end Schemes

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (u : a ⟶ b)
variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)

abbrev chartFirstGeom := projection_first_geom (polynomialProjection P a)
  (coefficientMap P (α.app a)) (coefficientMap P ((laurentUnderFunctor R).map u))
  (laurentProjection P a) ha

abbrev chartFirstSourceEq := projection_first_source_eq (polynomialProjection P a)
  (coefficientMap P (α.app a)) (coefficientMap P ((laurentUnderFunctor R).map u))
  (laurentProjection P a) ha

/-- The whole original coefficient-chart node retains that same projection association. -/
theorem chart_first_normal : BassH0Diagram.chartNodes P u α ha 9 =
    (⟨BinaryNormalizationSimplex.targetMap
      (coefficientMap P ((laurentUnderFunctor R).map u) ≫ coefficientMap P (α.app a))
      (polynomialProjection P a),
      eqToIso (chartFirstSourceEq P u α ha) ≪≫ BinaryNormalizationSimplex.total
        (coefficientMap P ((laurentUnderFunctor R).map u) ≫ coefficientMap P (α.app a))
        (polynomialProjection P a)⟩ : BassH0Diagram.Node P u) :=
  projection_first_normal (polynomialProjection P a) (coefficientMap P (α.app a))
    (polynomialProjection P b) (coefficientMap P (α.app b)) (coefficientMap P u)
    (coefficientMap P ((polynomialUnderFunctor R).map u))
    (coefficientMap P ((laurentUnderFunctor R).map u))
    (coefficientTransformation_naturality P (polynomialUnderCoefficient R) u)
    (coefficientTransformation_naturality P α u) (laurentProjection P a) ha

end Quillen.PerfectComplexes.BassH1Join
