/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientNativeKCharts

/-!
# Original coefficient Bass row comparisons

The actual chosen native K-equivalences identify the original common coefficient pair and
signed Laurent difference with the original native Bass maps. Both squares retain all
original pullbacks and the literal positive-minus-negative convention.
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

variable {R : CommRingCat.{u}} (P : Over (Spec R))

/-- The original polynomial coefficient pullback in both original chart factors. -/
def boundedFlatCoefficientPairHom (a : Under R) (n : ℕ) :
    BoundedFlatPerfectK (space (op P, a)) n →*
      BoundedFlatPerfectK (space (op P, (polynomialUnderFunctor R).obj a)) n ×
        BoundedFlatPerfectK (space (op P, (polynomialUnderFunctor R).obj a)) n :=
  (boundedFlatPerfectKPullback (polynomialProjection P a) n).prod
    (boundedFlatPerfectKPullback (polynomialProjection P a) n)

/-- Original positive Laurent pullback times inverse original negative Laurent pullback. -/
def boundedFlatCoefficientDifferenceHom (a : Under R) (n : ℕ) :
    BoundedFlatPerfectK (space (op P, (polynomialUnderFunctor R).obj a)) n ×
      BoundedFlatPerfectK (space (op P, (polynomialUnderFunctor R).obj a)) n →*
        BoundedFlatPerfectK (space (op P, (laurentUnderFunctor R).obj a)) n :=
  GroupMayerVietoris.difference (boundedFlatPerfectKPullback (laurentPlus P a) n)
    (boundedFlatPerfectKPullback (laurentMinus P a) n)

variable [CompactSpace P.left] (a : Under R)
local notation "X" => Opposite.unop (Functor.obj (boundedFlatCoefficientQuasiCompactRow P) a)

/-- The pair comparison uses the same original polynomial isomorphism in both factors. -/
def boundedFlatCoefficientNativePairKEquiv (n : ℕ) :
    BoundedFlatPerfectK (space (op P, (polynomialUnderFunctor R).obj a)) n ×
      BoundedFlatPerfectK (space (op P, (polynomialUnderFunctor R).obj a)) n ≃*
        PerfectK (Relative.polynomialFunctor.obj X).obj n ×
          PerfectK (Relative.polynomialFunctor.obj X).obj n :=
  MulEquiv.prodCongr (boundedFlatCoefficientNativePolynomialKEquiv P a n)
    (boundedFlatCoefficientNativePolynomialKEquiv P a n)

/-- The literal original common-corner square commutes. -/
theorem boundedFlatCoefficientPairHom_native (n : ℕ) :
    (boundedFlatCoefficientNativePairKEquiv P a n).toMonoidHom.comp
      (boundedFlatCoefficientPairHom P a n) =
      (coefficientPair X n).comp (boundedFlatPerfectKEquiv (X).obj n).toMonoidHom := by
  apply MonoidHom.ext
  intro x
  apply Prod.ext
  · exact (DFunLike.congr_fun (boundedFlatCoefficientNativeKEquiv_coefficient P a n) x).symm
  · exact (DFunLike.congr_fun (boundedFlatCoefficientNativeKEquiv_coefficient P a n) x).symm

/-- The signed difference square retains both original chart maps. -/
theorem boundedFlatCoefficientDifferenceHom_native (n : ℕ) :
    (boundedFlatCoefficientNativeLaurentKEquiv P a n).toMonoidHom.comp
      (boundedFlatCoefficientDifferenceHom P a n) =
      (laurentDifference X n).comp
        (boundedFlatCoefficientNativePairKEquiv P a n).toMonoidHom := by
  ext x
  change boundedFlatCoefficientNativeLaurentKEquiv P a n
      (boundedFlatPerfectKPullback (laurentPlus P a) n x.1 *
        (boundedFlatPerfectKPullback (laurentMinus P a) n x.2)⁻¹) =
    perfectKRestrict (Relative.plus.app X).hom n
      (boundedFlatCoefficientNativePolynomialKEquiv P a n x.1) *
        (perfectKRestrict (Relative.minus.app X).hom n
          (boundedFlatCoefficientNativePolynomialKEquiv P a n x.2))⁻¹
  rw [map_mul, map_inv]
  exact congrArg₂ (fun x y => x * y⁻¹)
    (DFunLike.congr_fun (boundedFlatCoefficientNativeKEquiv_plus P a n) x.1).symm
    (DFunLike.congr_fun (boundedFlatCoefficientNativeKEquiv_minus P a n) x.2).symm

end Quillen.PerfectComplexes
