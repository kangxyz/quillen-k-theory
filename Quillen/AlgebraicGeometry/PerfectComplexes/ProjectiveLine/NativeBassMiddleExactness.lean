/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeBassCharts
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeGlobalBundle

/-!
# Middle exactness of the native Bass coefficient row on qcqs schemes

The original global projective-bundle map has the polynomial coefficient sum on both charts.
Its bijectivity identifies the image of original projective restrictions with the coefficient
pair. Connective Mayer–Vietoris therefore proves Bass middle exactness, including degree zero.
-/
@[expose] public section
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes.ProjectiveLine.NativeBass
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative

attribute [local instance] Waldhausen.Additivity.KCommGroup

variable (X : QuasiCompactSchemes.{u}) [QuasiSeparatedSpace X.obj]

/-- The actual global two-summand equivalence identifies the original chart image. -/
theorem restrictionPair_range_eq_coefficientPair (n : ℕ) :
    (restrictionPair X n).range = (coefficientPair X n).range := by
  have hPhi (a b : PerfectK X.obj n) :
      restrictionPair X n (nativeGlobalTwoSummandKEquiv X n (a, b)) =
        coefficientPair X n (a * b) := by
    apply Prod.ext
    · exact (nativeTwoSummandKMap_chart X true n a b).trans (map_mul _ a b).symm
    · exact (nativeTwoSummandKMap_chart X false n a b).trans (map_mul _ a b).symm
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    let e := nativeGlobalTwoSummandKEquiv X n
    let c := e.symm y
    refine ⟨c.1 * c.2, ?_⟩
    exact (hPhi c.1 c.2).symm.trans (congrArg (restrictionPair X n) (e.apply_symm_apply y))
  · rintro ⟨y, rfl⟩
    refine ⟨nativeGlobalTwoSummandKEquiv X n (y, 1), ?_⟩
    simpa only [mul_one] using hPhi y 1

/-- Every connective native coefficient row is middle exact, including degree zero. -/
theorem range_coefficientPair_eq_ker_laurentDifference (n : ℕ) :
    (coefficientPair X n).range = (laurentDifference X n).ker := by
  rw [← restrictionPair_range_eq_coefficientPair]
  exact range_restrictionPair_eq_ker_laurentDifference X n

end Quillen.PerfectComplexes.ProjectiveLine.NativeBass
