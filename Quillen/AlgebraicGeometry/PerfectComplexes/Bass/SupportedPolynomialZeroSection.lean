/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.OpenPairs.PolynomialZeroSection
public import Quillen.AlgebraicGeometry.PerfectComplexes.Bass.SupportedGroups

/-!
# Split polynomial common corners with actual auxiliary support

The original zero section on both entries of the scheme/open pair splits
polynomial pullback in every supported Bass degree. It also splits the
original common-corner arrow and shows that this arrow is killed by the actual
signed chart difference. Only the ambient scheme is required quasi-compact;
the vanishing open remains unrestricted. Middle exactness and spectral seed
stabilization are separate obligations.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Quillen.Scheme
universe u
namespace Quillen.PerfectComplexes.Bass

/-- Original polynomial zero evaluation in every supported recursive negative group. -/
def supportedNegativeKPolynomialEvaluation (A : QuasiCompactOpenPairs.{u}) (n : ℕ) :
    supportedNegativeK (Scheme.Bass.pairPolynomialFunctor.obj A) n ⟶ supportedNegativeK A n :=
  supportedNegativeKPullback (Scheme.Bass.pairPolynomialZero.app A) n

@[reassoc (attr := simp)]
theorem supportedNegativeKPolynomialPullback_evaluation (A : QuasiCompactOpenPairs.{u}) (n : ℕ) :
    supportedNegativeKPullback (Scheme.Bass.pairPolynomialProjection.app A) n ≫
      supportedNegativeKPolynomialEvaluation A n = 𝟙 (supportedNegativeK A n) := by
  rw [supportedNegativeKPolynomialEvaluation, ← supportedNegativeKPullback_comp,
    Scheme.Bass.pairPolynomialZero_projection]
  exact (supportedNegativeKFunctor n).map_id _

/-- Supported polynomial projection pullback is injective at every recursive stage. -/
theorem supportedNegativeKPolynomialPullback_injective (A : QuasiCompactOpenPairs.{u}) (n : ℕ) :
    Function.Injective
      (supportedNegativeKPullback (Scheme.Bass.pairPolynomialProjection.app A) n) := by
  have h : Function.LeftInverse (supportedNegativeKPolynomialEvaluation A n)
      (supportedNegativeKPullback (Scheme.Bass.pairPolynomialProjection.app A) n) := fun x =>
    ConcreteCategory.congr_hom (supportedNegativeKPolynomialPullback_evaluation A n) x
  exact h.injective

/-- Original supported common-corner pullback into the two polynomial chart groups. -/
def supportedNegativeKCommonCorner (A : QuasiCompactOpenPairs.{u}) (n : ℕ) :
    supportedNegativeK A n ⟶ supportedNegativeK (Scheme.Bass.pairPolynomialFunctor.obj A) n ⊞
      supportedNegativeK (Scheme.Bass.pairPolynomialFunctor.obj A) n :=
  biprod.lift (supportedNegativeKPullback (Scheme.Bass.pairPolynomialProjection.app A) n)
    (supportedNegativeKPullback (Scheme.Bass.pairPolynomialProjection.app A) n)

@[reassoc (attr := simp)]
theorem supportedNegativeKCommonCorner_evaluation (A : QuasiCompactOpenPairs.{u}) (n : ℕ) :
    supportedNegativeKCommonCorner A n ≫ biprod.fst ≫
      supportedNegativeKPolynomialEvaluation A n = 𝟙 (supportedNegativeK A n) := by
  simp [supportedNegativeKCommonCorner]

/-- The actual supported common corner is split injective, without a compact-open premise. -/
theorem supportedNegativeKCommonCorner_injective (A : QuasiCompactOpenPairs.{u}) (n : ℕ) :
    Function.Injective (supportedNegativeKCommonCorner A n) := by
  have h : Function.LeftInverse (biprod.fst ≫ supportedNegativeKPolynomialEvaluation A n)
      (supportedNegativeKCommonCorner A n) := fun x =>
    ConcreteCategory.congr_hom (supportedNegativeKCommonCorner_evaluation A n) x
  exact h.injective

/-- Both supported Laurent charts have the original common projection, with opposite signs. -/
@[reassoc (attr := simp)]
theorem supportedNegativeKCommonCorner_difference (A : QuasiCompactOpenPairs.{u}) (n : ℕ) :
    supportedNegativeKCommonCorner A n ≫
      Quillen.Bass.TwoChart.polynomialDifference (NatTrans.op Scheme.Bass.pairPlus)
        (NatTrans.op Scheme.Bass.pairMinus) (supportedNegativeKFunctor n) (op A) = 0 := by
  simp only [supportedNegativeKCommonCorner, Quillen.Bass.TwoChart.polynomialDifference,
    biprod.lift_desc, Preadditive.comp_neg, supportedNegativeKPullback, NatTrans.op_app,
    ← Functor.map_comp, ← op_comp, Scheme.Bass.pairPlus_projection,
    Scheme.Bass.pairMinus_projection, add_neg_cancel]

end Quillen.PerfectComplexes.Bass

namespace Quillen.PerfectComplexes

/-- The same actual pair zero section splits supported perfect K in every nonnegative degree. -/
theorem perfectSupportedKPolynomialPullback_evaluation (A : QuasiCompactOpenPairs.{u}) (n : ℕ) :
    (perfectSupportedKPullback (Quillen.Scheme.Bass.pairPolynomialZero.app A) n).comp
      (perfectSupportedKPullback (Quillen.Scheme.Bass.pairPolynomialProjection.app A) n) =
      MonoidHom.id (PerfectSupportedK A.obj.obj.hom n) := by
  rw [← perfectSupportedKPullback_comp, Quillen.Scheme.Bass.pairPolynomialZero_projection]
  exact perfectSupportedKPullback_id A n

/-- Original supported perfect K projection pullback is injective, including degree zero. -/
theorem perfectSupportedKPolynomialPullback_injective (A : QuasiCompactOpenPairs.{u}) (n : ℕ) :
    Function.Injective
      (perfectSupportedKPullback (Quillen.Scheme.Bass.pairPolynomialProjection.app A) n) := by
  have h : Function.LeftInverse
      (perfectSupportedKPullback (Quillen.Scheme.Bass.pairPolynomialZero.app A) n)
      (perfectSupportedKPullback (Quillen.Scheme.Bass.pairPolynomialProjection.app A) n) := fun x =>
    congrArg (fun f => f x) (perfectSupportedKPolynomialPullback_evaluation A n)
  exact h.injective

end Quillen.PerfectComplexes
