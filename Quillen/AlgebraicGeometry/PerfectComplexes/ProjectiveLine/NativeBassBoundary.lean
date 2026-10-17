/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeBassMiddleExactness
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeBassExactSequence
public import Quillen.AlgebraicGeometry.PerfectComplexes.Bass.PolynomialZeroSection

/-!
# The original first-coordinate global Bass boundary in every connective degree

For every qcqs base the original global Phi coordinates retain the unchanged native
Mayer–Vietoris boundary. Zero evaluation supplies the first injection, while exactness and the
original global two-summand inverse give its kernel and surjectivity in every connective degree.
-/
@[expose] public section
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.ProjectiveLine.NativeBass
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.ProjectiveLine
attribute [local instance] Waldhausen.Additivity.KCommGroup
variable (X : QuasiCompactSchemes.{u})

/-- Actual zero evaluation gives the first injection in every native coefficient row. -/
theorem coefficientPair_injective (n : ℕ) : Function.Injective (coefficientPair X n) := by
  intro a b h
  apply perfectKPolynomialPullback_injective X n
  have hp := congrArg Prod.fst h
  change perfectKFlatPullback (Relative.polynomialProjection.app X).hom n a =
    perfectKFlatPullback (Relative.polynomialProjection.app X).hom n b at hp
  simpa only [perfectKPullback_eq_flatPullback] using hp

variable [QuasiSeparatedSpace X.obj]

/-- The same global Phi coordinates have their sum on both original native charts. -/
theorem restrictionPair_Phi (n : ℕ) (a b : PerfectK X.obj n) :
    restrictionPair X n (nativeGlobalTwoSummandKEquiv X n (a, b)) =
      coefficientPair X n (a * b) := by
  apply Prod.ext
  · exact (nativeTwoSummandKMap_chart X true n a b).trans (map_mul _ a b).symm
  · exact (nativeTwoSummandKMap_chart X false n a b).trans (map_mul _ a b).symm

/-- Coordinates of the unchanged original projective connecting map. -/
def connectingCoefficients (n : ℕ) :
    PerfectK (Relative.laurentFunctor.obj X).obj (n + 1) →*
      PerfectK X.obj n × PerfectK X.obj n :=
  (nativeGlobalTwoSummandKEquiv X n).symm.toMonoidHom.comp (projectiveConnecting X n)

/-- The original first-coordinate Bass boundary. -/
def positiveBassBoundary (n : ℕ) :
    PerfectK (Relative.laurentFunctor.obj X).obj (n + 1) →* PerfectK X.obj n :=
  (MonoidHom.fst _ _).comp (connectingCoefficients X n)

/-- Original chart restriction forces the actual boundary coordinates to multiply to one. -/
theorem connectingCoefficients_product_eq_one (n : ℕ)
    (x : PerfectK (Relative.laurentFunctor.obj X).obj (n + 1)) :
    (connectingCoefficients X n x).1 * (connectingCoefficients X n x).2 = 1 := by
  let e := nativeGlobalTwoSummandKEquiv X n
  let y := projectiveConnecting X n x
  let c := connectingCoefficients X n x
  have hy : y ∈ (restrictionPair X n).ker := by
    rw [← range_projectiveConnecting_eq_ker_restrictionPair]
    exact ⟨x, rfl⟩
  have hp : coefficientPair X n (c.1 * c.2) = 1 := by
    calc
      _ = restrictionPair X n (e c) := (restrictionPair_Phi X n c.1 c.2).symm
      _ = restrictionPair X n y := congrArg (restrictionPair X n) (e.apply_symm_apply y)
      _ = 1 := hy
  exact coefficientPair_injective X n (hp.trans (map_one (coefficientPair X n)).symm)

/-- The unchanged scalar Bass boundary has the same kernel as the projective boundary. -/
theorem positiveBassBoundary_ker (n : ℕ) :
    (positiveBassBoundary X n).ker = (projectiveConnecting X n).ker := by
  ext x
  change positiveBassBoundary X n x = 1 ↔ projectiveConnecting X n x = 1
  constructor
  · intro hx
    have hc : connectingCoefficients X n x = 1 := by
      apply Prod.ext
      · exact hx
      · change (connectingCoefficients X n x).2 = 1
        have h := connectingCoefficients_product_eq_one X n x
        change (connectingCoefficients X n x).1 = 1 at hx
        simpa only [hx, one_mul] using h
    let e := nativeGlobalTwoSummandKEquiv X n
    have h := congrArg e hc
    change e (e.symm (projectiveConnecting X n x)) = e 1 at h
    simpa only [MulEquiv.apply_symm_apply, map_one] using h
  · intro hx
    change ((nativeGlobalTwoSummandKEquiv X n).symm (projectiveConnecting X n x)).1 = 1
    rw [hx, map_one]
    rfl

/-- Exactness at the actual Laurent K-group, through the unchanged first-coordinate boundary. -/
theorem range_laurentDifference_eq_ker_positiveBassBoundary (n : ℕ) :
    (laurentDifference X (n + 1)).range = (positiveBassBoundary X n).ker := by
  rw [positiveBassBoundary_ker]
  exact range_laurentDifference_eq_ker_projectiveConnecting X n

/-- Every original coefficient is hit by the original first-coordinate boundary. -/
theorem positiveBassBoundary_surjective (n : ℕ) :
    Function.Surjective (positiveBassBoundary X n) := by
  intro a
  let e := nativeGlobalTwoSummandKEquiv X n
  have hk : e (a, a⁻¹) ∈ (restrictionPair X n).ker := by
    change restrictionPair X n (e (a, a⁻¹)) = 1
    rw [restrictionPair_Phi, mul_inv_cancel, map_one]
  have hi : e (a, a⁻¹) ∈ (projectiveConnecting X n).range := by
    rw [range_projectiveConnecting_eq_ker_restrictionPair]
    exact hk
  obtain ⟨x, hx⟩ := hi
  refine ⟨x, ?_⟩
  change (e.symm (projectiveConnecting X n x)).1 = a
  rw [hx, MulEquiv.symm_apply_apply]

end Quillen.PerfectComplexes.ProjectiveLine.NativeBass
