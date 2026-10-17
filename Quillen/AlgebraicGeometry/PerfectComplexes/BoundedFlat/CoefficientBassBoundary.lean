/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassChartComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientNativeBoundaryCoordinates
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeBassBoundary

/-!
# The original first-coordinate Bass boundary on the coefficient row

The actual polynomial and Laurent comparisons transport the unchanged first-coordinate
projective boundary to the original bounded-flat coefficient groups. Its exact kernel and
literal inverse-unit section hold over every compact quasi-separated coefficient scheme.
No affine hypothesis or flatness assumption on coefficient maps is used. Naturality will be
obtained from the natural inverse-unit isomorphism of the original Bass quotient.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.ProjectiveLine Quillen.PerfectComplexes.ProjectiveLine
open Quillen.PerfectComplexes.ProjectiveLine.NativeBass
universe u
namespace Quillen.PerfectComplexes
attribute [local instance] Waldhausen.Additivity.KCommGroup

variable {R : CommRingCat.{u}} (P : Over (Spec R)) [CompactSpace P.left]
variable [QuasiSeparatedSpace P.left] (a : Under R)
local notation "X" => Opposite.unop (Functor.obj (boundedFlatCoefficientQuasiCompactRow P) a)
local instance coefficientBassBoundary_quasiSeparated : QuasiSeparatedSpace (X).obj :=
  quasiSeparatedSpace_space (op P, a)

/-- Transport of the original first-coordinate boundary, using the actual chosen K-maps. -/
def boundedFlatCoefficientPositiveBassBoundary (n : ℕ) :
    BoundedFlatPerfectK (space (op P, (laurentUnderFunctor R).obj a)) (n + 1) →*
      BoundedFlatPerfectK (space (op P, a)) n :=
  (boundedFlatPerfectKEquiv (X).obj n).symm.toMonoidHom.comp
    ((positiveBassBoundary X n).comp
      (boundedFlatCoefficientNativeLaurentKEquiv P a (n + 1)).toMonoidHom)

/-- The native comparison square retains exactly the original first-coordinate boundary. -/
theorem boundedFlatCoefficientPositiveBassBoundary_native (n : ℕ) :
    (boundedFlatPerfectKEquiv (X).obj n).toMonoidHom.comp
      (boundedFlatCoefficientPositiveBassBoundary P a n) =
      (positiveBassBoundary X n).comp
        (boundedFlatCoefficientNativeLaurentKEquiv P a (n + 1)).toMonoidHom := by
  ext x
  exact (boundedFlatPerfectKEquiv (X).obj n).apply_symm_apply _

/-- Exactness at the original coefficient Laurent group, with its original boundary. -/
theorem boundedFlatCoefficientDifference_range_eq_bassBoundary_ker (n : ℕ) :
    (boundedFlatCoefficientDifferenceHom P a (n + 1)).range =
      (boundedFlatCoefficientPositiveBassBoundary P a n).ker := by
  have h : Function.MulExact (laurentDifference X (n + 1)) (positiveBassBoundary X n) :=
    MonoidHom.mulExact_iff.mpr
      (range_laurentDifference_eq_ker_positiveBassBoundary X n).symm
  have ht := (MonoidHom.mulExact_iff_of_surjective_of_bijective_of_injective
    (boundedFlatCoefficientDifferenceHom P a (n + 1))
    (boundedFlatCoefficientPositiveBassBoundary P a n)
    (laurentDifference X (n + 1)) (positiveBassBoundary X n)
    (boundedFlatCoefficientNativePairKEquiv P a (n + 1)).toMonoidHom
    (boundedFlatCoefficientNativeLaurentKEquiv P a (n + 1)).toMonoidHom
    (boundedFlatPerfectKEquiv (X).obj n).toMonoidHom
    (boundedFlatCoefficientDifferenceHom_native P a (n + 1)).symm
    (boundedFlatCoefficientPositiveBassBoundary_native P a n).symm
    (boundedFlatCoefficientNativePairKEquiv P a (n + 1)).surjective
    (boundedFlatCoefficientNativeLaurentKEquiv P a (n + 1)).bijective
    (boundedFlatPerfectKEquiv (X).obj n).injective).mpr h
  exact (MonoidHom.mulExact_iff.mp ht).symm

/-- The original forward unit retains the inversion sign in the actual coefficient row. -/
theorem boundedFlatCoefficientPositiveBassBoundary_comp_forward (n : ℕ) :
    (boundedFlatCoefficientPositiveBassBoundary P a n).comp
      (boundedFlatCoefficientLaurentKOperation P a n) = invMonoidHom := by
  ext x
  apply (boundedFlatPerfectKEquiv (X).obj n).injective
  change (boundedFlatPerfectKEquiv (X).obj n)
      ((boundedFlatPerfectKEquiv (X).obj n).symm _) = _
  rw [MulEquiv.apply_symm_apply]
  change positiveBassBoundary X n
    (boundedFlatCoefficientNativeLaurentKEquiv P a (n + 1)
      (boundedFlatCoefficientLaurentKOperation P a n x)) =
    (boundedFlatPerfectKEquiv (X).obj n) (x⁻¹)
  rw [map_inv]
  have h := DFunLike.congr_fun (boundedFlatCoefficientNativeBoundary_comp_forward P a n) x
  change projectiveConnecting X n
      (boundedFlatCoefficientNativeLaurentKEquiv P a (n + 1)
        (boundedFlatCoefficientLaurentKOperation P a n x)) =
    nativeTwoSummandKMap X n
      (((boundedFlatPerfectKEquiv (X).obj n) x)⁻¹,
        (boundedFlatPerfectKEquiv (X).obj n) x) at h
  change ((nativeGlobalTwoSummandKEquiv X n).symm (projectiveConnecting X n _)).1 = _
  rw [h]
  exact congrArg Prod.fst ((nativeGlobalTwoSummandKEquiv X n).symm_apply_apply _)

/-- The literal inverse Laurent unit splits the same original first-coordinate boundary. -/
theorem boundedFlatCoefficientPositiveBassBoundary_comp_inverse (n : ℕ) :
    (boundedFlatCoefficientPositiveBassBoundary P a n).comp
      (boundedFlatCoefficientInverseLaurentKOperation P a n) =
      MonoidHom.id (BoundedFlatPerfectK (space (op P, a)) n) := by
  ext x
  apply (boundedFlatPerfectKEquiv (X).obj n).injective
  change (boundedFlatPerfectKEquiv (X).obj n)
      ((boundedFlatPerfectKEquiv (X).obj n).symm _) = _
  rw [MulEquiv.apply_symm_apply]
  have h := DFunLike.congr_fun (boundedFlatCoefficientNativeBoundary_comp_inverse P a n) x
  change projectiveConnecting X n
      (boundedFlatCoefficientNativeLaurentKEquiv P a (n + 1)
        (boundedFlatCoefficientInverseLaurentKOperation P a n x)) =
    nativeTwoSummandKMap X n
      ((boundedFlatPerfectKEquiv (X).obj n) x,
        ((boundedFlatPerfectKEquiv (X).obj n) x)⁻¹) at h
  change ((nativeGlobalTwoSummandKEquiv X n).symm
    (projectiveConnecting X n (boundedFlatCoefficientNativeLaurentKEquiv P a (n + 1)
      (boundedFlatCoefficientInverseLaurentKOperation P a n x)))).1 =
    (boundedFlatPerfectKEquiv (X).obj n) x
  rw [h]
  exact congrArg Prod.fst ((nativeGlobalTwoSummandKEquiv X n).symm_apply_apply _)

/-- Every original coefficient is in the image of the same first-coordinate boundary. -/
theorem boundedFlatCoefficientPositiveBassBoundary_surjective (n : ℕ) :
    Function.Surjective (boundedFlatCoefficientPositiveBassBoundary P a n) := by
  intro x
  exact ⟨boundedFlatCoefficientInverseLaurentKOperation P a n x,
    DFunLike.congr_fun (boundedFlatCoefficientPositiveBassBoundary_comp_inverse P a n) x⟩

end Quillen.PerfectComplexes
