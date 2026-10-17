/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassChartComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeBassMiddleExactness

/-!
# Middle exactness of the original coefficient Bass row

The exact native global row transports through the original chosen polynomial/Laurent
isomorphisms and actual bounded-flat inclusions. This includes degree zero for every compact,
quasi-separated coefficient row, with no affine or flat coefficient-map hypothesis.
-/
@[expose] public section
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.PerfectComplexes.ProjectiveLine.NativeBass
universe u
namespace Quillen.PerfectComplexes
attribute [local instance] Waldhausen.Additivity.KCommGroup

variable {R : CommRingCat.{u}} (P : Over (Spec R)) [CompactSpace P.left]
variable [QuasiSeparatedSpace P.left] (a : Under R)
local notation "X" => Opposite.unop (Functor.obj (boundedFlatCoefficientQuasiCompactRow P) a)
local instance coefficientMiddle_quasiSeparated : QuasiSeparatedSpace (X).obj :=
  quasiSeparatedSpace_space (op P, a)

/-- Global middle exactness for both original coefficient charts, including degree zero. -/
theorem boundedFlatCoefficientPair_range_eq_difference_ker (n : ℕ) :
    (boundedFlatCoefficientPairHom P a n).range =
      (boundedFlatCoefficientDifferenceHom P a n).ker := by
  have h : Function.MulExact (coefficientPair X n) (laurentDifference X n) :=
    MonoidHom.mulExact_iff.mpr (range_coefficientPair_eq_ker_laurentDifference X n).symm
  have ht := (MonoidHom.mulExact_iff_of_surjective_of_bijective_of_injective
    (boundedFlatCoefficientPairHom P a n) (boundedFlatCoefficientDifferenceHom P a n)
    (coefficientPair X n) (laurentDifference X n)
    (boundedFlatPerfectKEquiv (X).obj n).toMonoidHom
    (boundedFlatCoefficientNativePairKEquiv P a n).toMonoidHom
    (boundedFlatCoefficientNativeLaurentKEquiv P a n).toMonoidHom
    (boundedFlatCoefficientPairHom_native P a n).symm
    (boundedFlatCoefficientDifferenceHom_native P a n).symm
    (boundedFlatPerfectKEquiv (X).obj n).surjective
    (boundedFlatCoefficientNativePairKEquiv P a n).bijective
    (boundedFlatCoefficientNativeLaurentKEquiv P a n).injective).mpr h
  exact (MonoidHom.mulExact_iff.mp ht).symm

end Quillen.PerfectComplexes
