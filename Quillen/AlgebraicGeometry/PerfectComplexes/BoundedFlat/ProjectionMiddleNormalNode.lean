/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1MiddleJoinFace

/-! The actual normalized middle node of an original projection rectangle. -/
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

include hq hr in
/-- The original square and projection equations give the exact middle total. -/
theorem projection_middle_geom : c ≫ r = q' ≫ b ≫ p := by
  calc
    _ = c ≫ q ≫ p := congrArg (fun k ↦ c ≫ k) hr.symm
    _ = _ := by rw [← Category.assoc, hq, Category.assoc]

include hq hr in
theorem projection_middle_source_eq : (ProjectionReference.reference c r).functor =
    (BinaryNormalizationSimplex.sourceMap q' (b ≫ p)).functor :=
  congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
    (congrArg boundedFlatNormalizedPullback (projection_middle_geom p q q' b c hq r hr))

theorem projection_middle_normal_functor :
    (ProjectionReference.nodes p q p' q' a b c hp hq r hr 5).1.functor =
      (BinaryNormalizationSimplex.targetMap q' (b ≫ p)).functor := rfl

/-- The actual middle reference is its unchanged native source transport and normalization. -/
theorem projection_middle_normal_reference :
    (ProjectionReference.nodes p q p' q' a b c hp hq r hr 5).2 =
      eqToIso (projection_middle_source_eq p q q' b c hq r hr) ≪≫
        BinaryNormalizationSimplex.total q' (b ≫ p) := by
  change eqToIso (ProjectionReference.anchor p q c r hr) ≪≫
    (smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
      (DoubleSquareTrack.middle_eq p q q' b c hq).symm)) ≪≫
      smallIso (boundedFlatNormalizedPullbackCompIso q' (b ≫ p))) = _
  rw [smallIso_eqToIso, ← Iso.trans_assoc, eqToIso_trans]
  rfl

/-- Full dependent middle node, not merely its normalized endpoint functor. -/
theorem projection_middle_normal :
    ProjectionReference.nodes p q p' q' a b c hp hq r hr 5 =
      (⟨BinaryNormalizationSimplex.targetMap q' (b ≫ p),
        eqToIso (projection_middle_source_eq p q q' b c hq r hr) ≪≫
          BinaryNormalizationSimplex.total q' (b ≫ p)⟩ : ProjectionReference.Node c r) := by
  apply Sigma.ext (Model.Hom.ext
    (projection_middle_normal_functor p q p' q' a b c hp hq r hr))
  exact heq_of_eq (projection_middle_normal_reference p q p' q' a b c hp hq r hr)
end Schemes

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (u : a ⟶ b)
variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)

abbrev chartMiddleSourceEq := projection_middle_source_eq
  (polynomialProjection P a) (coefficientMap P (α.app a)) (coefficientMap P (α.app b))
  (coefficientMap P ((polynomialUnderFunctor R).map u))
  (coefficientMap P ((laurentUnderFunctor R).map u))
  (coefficientTransformation_naturality P α u) (laurentProjection P a) ha

/-- The full actual coefficient-chart middle node retains that same geometric normalization. -/
theorem chart_middle_normal : BassH0Diagram.chartNodes P u α ha 5 =
    (⟨BinaryNormalizationSimplex.targetMap (coefficientMap P (α.app b))
      (coefficientMap P ((polynomialUnderFunctor R).map u) ≫ polynomialProjection P a),
      eqToIso (chartMiddleSourceEq P u α ha) ≪≫ BinaryNormalizationSimplex.total
        (coefficientMap P (α.app b))
        (coefficientMap P ((polynomialUnderFunctor R).map u) ≫ polynomialProjection P a)⟩ :
      BassH0Diagram.Node P u) :=
  projection_middle_normal
    (polynomialProjection P a) (coefficientMap P (α.app a))
    (polynomialProjection P b) (coefficientMap P (α.app b))
    (coefficientMap P u) (coefficientMap P ((polynomialUnderFunctor R).map u))
    (coefficientMap P ((laurentUnderFunctor R).map u))
    (coefficientTransformation_naturality P (polynomialUnderCoefficient R) u)
    (coefficientTransformation_naturality P α u) (laurentProjection P a) ha

end Quillen.PerfectComplexes.BassH1Join
