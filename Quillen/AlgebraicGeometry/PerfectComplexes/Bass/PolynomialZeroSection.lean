/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.PolynomialZeroSection
public import Quillen.AlgebraicGeometry.PerfectComplexes.BassNegativeGroups

/-!
# Original zero evaluation in the Bass groups

The actual polynomial zero section splits the original projection pullback in
every recursive negative degree. The common-corner map of the two-chart
sequence is therefore split injective, and its composite with the original
chart difference is zero. This proves the left injection and its specified
splitting; middle exactness and spectral seed stabilization remain separate.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
universe u

namespace Quillen.PerfectComplexes.Bass

/-- Actual polynomial evaluation at zero in each original recursive negative group. -/
def negativeKPolynomialEvaluation (X : QuasiCompactSchemes.{u}) (n : ℕ) :
    negativeK (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.polynomialFunctor.obj X) n ⟶
      negativeK X n :=
  negativeKPullback (Scheme.Bass.polynomialZero.app X) n

@[reassoc (attr := simp)]
theorem negativeKPolynomialPullback_evaluation (X : QuasiCompactSchemes.{u}) (n : ℕ) :
    negativeKPullback (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.polynomialProjection.app
      X) n ≫
      negativeKPolynomialEvaluation X n = 𝟙 (negativeK X n) := by
  rw [negativeKPolynomialEvaluation, ← negativeKPullback_comp,
    Scheme.Bass.polynomialZero_projection]
  exact (negativeKFunctor n).map_id _

/-- Projection pullback is injective in every original Bass degree, without regularity. -/
theorem negativeKPolynomialPullback_injective (X : QuasiCompactSchemes.{u}) (n : ℕ) :
    Function.Injective (negativeKPullback
      (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.polynomialProjection.app X) n) := by
  have h : Function.LeftInverse (negativeKPolynomialEvaluation X n)
      (negativeKPullback
        (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.polynomialProjection.app X) n) := fun x
        =>
    ConcreteCategory.congr_hom (negativeKPolynomialPullback_evaluation X n) x
  exact h.injective

/-- The actual common corner enters both original polynomial chart groups. -/
def negativeKCommonCorner (X : QuasiCompactSchemes.{u}) (n : ℕ) :
    negativeK X n ⟶ negativeK
      (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.polynomialFunctor.obj X) n ⊞
      negativeK (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.polynomialFunctor.obj X) n :=
  biprod.lift (negativeKPullback
    (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.polynomialProjection.app X) n)
    (negativeKPullback (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.polynomialProjection.app
      X) n)

@[reassoc (attr := simp)]
theorem negativeKCommonCorner_evaluation (X : QuasiCompactSchemes.{u}) (n : ℕ) :
    negativeKCommonCorner X n ≫ biprod.fst ≫ negativeKPolynomialEvaluation X n =
      𝟙 (negativeK X n) := by
  simp [negativeKCommonCorner]

/-- The original two-chart common-corner arrow is split injective at every recursive stage. -/
theorem negativeKCommonCorner_injective (X : QuasiCompactSchemes.{u}) (n : ℕ) :
    Function.Injective (negativeKCommonCorner X n) := by
  have h : Function.LeftInverse (biprod.fst ≫ negativeKPolynomialEvaluation X n)
      (negativeKCommonCorner X n) := fun x =>
    ConcreteCategory.congr_hom (negativeKCommonCorner_evaluation X n) x
  exact h.injective

/-- Both original Laurent charts retain the same projection, so the common corner is killed. -/
@[reassoc (attr := simp)]
theorem negativeKCommonCorner_difference (X : QuasiCompactSchemes.{u}) (n : ℕ) :
    negativeKCommonCorner X n ≫
      Quillen.Bass.TwoChart.polynomialDifference (NatTrans.op
        AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.plus)
        (NatTrans.op AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus) (negativeKFunctor n)
          (op X) = 0 := by
  simp only [negativeKCommonCorner, Quillen.Bass.TwoChart.polynomialDifference,
    biprod.lift_desc, Preadditive.comp_neg, negativeKPullback, NatTrans.op_app,
    ← Functor.map_comp, ← op_comp,
      AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.plus_projection,
    AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus_projection, add_neg_cancel]

end Quillen.PerfectComplexes.Bass

namespace Quillen.PerfectComplexes

/-- The same actual zero section splits perfect K pullback in all nonnegative degrees. -/
theorem perfectKPolynomialPullback_evaluation (X : QuasiCompactSchemes.{u}) (n : ℕ) :
    (perfectKPullback (AlgebraicGeometry.Scheme.Bass.polynomialZero.app X).hom n).comp
      (perfectKPullback
        (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.polynomialProjection.app X).hom n) =
      MonoidHom.id (PerfectK X.obj n) := by
  rw [← perfectKPullback_comp]
  have h := congrArg (fun f => f.hom) (AlgebraicGeometry.Scheme.Bass.polynomialZero_projection X)
  change (AlgebraicGeometry.Scheme.Bass.polynomialZero.app X).hom ≫
    (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.polynomialProjection.app X).hom = 𝟙 X.obj
      at h
  rw [h]
  exact perfectKPullback_id X.obj n

/-- Original perfect K projection pullback is injective, including degree zero. -/
theorem perfectKPolynomialPullback_injective (X : QuasiCompactSchemes.{u}) (n : ℕ) :
    Function.Injective
      (perfectKPullback
        (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.polynomialProjection.app X).hom n) :=
        by
  have h : Function.LeftInverse
      (perfectKPullback (AlgebraicGeometry.Scheme.Bass.polynomialZero.app X).hom n)
      (perfectKPullback
        (AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.polynomialProjection.app X).hom n) :=
        fun x =>
    congrArg (fun f => f x) (perfectKPolynomialPullback_evaluation X n)
  exact h.injective

end Quillen.PerfectComplexes
