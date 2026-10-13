/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionModel
public import Quillen.Waldhausen.Functoriality.ExactEquivalence

/-!
# Actual supported evaluation into the original common-universe model

The genuine supported evaluation equivalence followed by the existing universe-lifting
equivalence is exact in both directions.
The independently chosen geometric zero requires canonical zero normalization. The explicit
normalization iso transports the genuine equivalence and gives a chosen-zero Model map; no equality
between independent zeros is assumed. Coefficient naturality remains separate.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
attribute [local irreducible] boundedFlatAffineOriginalEvaluation
  boundedFlatAffineSupportedSectionEquivalence boundedFlatAffineSupportedEvaluation

/-- The proved original supported equivalence followed by the actual common-universe equivalence.
-/
def boundedFlatAffineSupportedSectionSmallEquivalence :
    BoundedFlatAffineSupportedSections j ≌
      SmallModel (boundedFlatPerfectSupported j).FullSubcategory :=
  (boundedFlatAffineSupportedSectionEquivalence j).trans AsSmall.equiv

/-- Forward evaluation into the existing original small model is exact. -/
theorem boundedFlatAffineSupportedSectionSmallEquivalence_exact :
    IsExact (boundedFlatAffineSupportedSectionWaldhausen j).cof
      (boundedFlatAffineSupportedSectionWaldhausen j).weq
      (boundedFlatPerfectSupportedWaldhausen j).smallModel.cof
      (boundedFlatPerfectSupportedWaldhausen j).smallModel.weq
      (boundedFlatAffineSupportedSectionSmallEquivalence j).functor := by
  change IsExact _ _ _ _ ((boundedFlatAffineSupportedSectionEquivalence j).functor ⋙ AsSmall.up)
  rw [boundedFlatAffineSupportedSectionEquivalence_functor]
  exact (boundedFlatAffineSupportedEvaluation_exact j).comp
    (boundedFlatPerfectSupportedWaldhausen j).smallModel_up_exact

/-- The original inverse equivalence followed by universe lowering is exact as well. -/
theorem boundedFlatAffineSupportedSectionSmallEquivalence_inverse_exact :
    IsExact (boundedFlatPerfectSupportedWaldhausen j).smallModel.cof
      (boundedFlatPerfectSupportedWaldhausen j).smallModel.weq
      (boundedFlatAffineSupportedSectionWaldhausen j).cof
      (boundedFlatAffineSupportedSectionWaldhausen j).weq
      (boundedFlatAffineSupportedSectionSmallEquivalence j).inverse :=
  (boundedFlatPerfectSupportedWaldhausen j).smallModel_down_exact.comp
    (boundedFlatAffineSupportedSectionEquivalence_inverse_exact j)

/-- The actual normalization iso from unchanged evaluation and original universe lifting. -/
def boundedFlatAffineSupportedSectionEvaluationNormalizationIso :
    (boundedFlatAffineSupportedSectionSmallEquivalence j).functor ≅
      Quillen.rebaseFunctor (boundedFlatAffineSupportedSectionSmallEquivalence j).functor
        (boundedFlatAffineSupportedSectionWaldhausen j).zero
        (boundedFlatPerfectSupportedWaldhausen j).smallModel.zero
        (((boundedFlatAffineSupportedSectionSmallEquivalence_exact j).zero
          (boundedFlatAffineSupportedSectionWaldhausen j).isZero).iso
          (boundedFlatPerfectSupportedWaldhausen j).smallModel.isZero) :=
  Quillen.rebaseFunctorIso _ _ _ _

/-- The genuine original equivalence transported through precisely its zero normalization. -/
def boundedFlatAffineSupportedSectionNormalizedEquivalence :
    BoundedFlatAffineSupportedSections j ≌
      SmallModel (boundedFlatPerfectSupported j).FullSubcategory :=
  (boundedFlatAffineSupportedSectionSmallEquivalence j).changeFunctor
    (boundedFlatAffineSupportedSectionEvaluationNormalizationIso j)

/-- The canonically normalized original evaluation remains exact. -/
theorem boundedFlatAffineSupportedSectionNormalizedEquivalence_exact :
    IsExact (boundedFlatAffineSupportedSectionWaldhausen j).cof
      (boundedFlatAffineSupportedSectionWaldhausen j).weq
      (boundedFlatPerfectSupportedWaldhausen j).smallModel.cof
      (boundedFlatPerfectSupportedWaldhausen j).smallModel.weq
      (boundedFlatAffineSupportedSectionNormalizedEquivalence j).functor :=
  (boundedFlatAffineSupportedSectionSmallEquivalence_exact j).rebase

/-- Changing the forward functor retains the original exact inverse literally. -/
theorem boundedFlatAffineSupportedSectionNormalizedEquivalence_inverse_exact :
    IsExact (boundedFlatPerfectSupportedWaldhausen j).smallModel.cof
      (boundedFlatPerfectSupportedWaldhausen j).smallModel.weq
      (boundedFlatAffineSupportedSectionWaldhausen j).cof
      (boundedFlatAffineSupportedSectionWaldhausen j).weq
      (boundedFlatAffineSupportedSectionNormalizedEquivalence j).inverse :=
  boundedFlatAffineSupportedSectionSmallEquivalence_inverse_exact j

/-- Canonically zero-normalized evaluation gives a map into the original supported model. -/
def boundedFlatAffineSupportedSectionEvaluationModelMap :
    boundedFlatAffineSupportedSectionModel j ⟶ modelOf (boundedFlatPerfectSupportedWaldhausen j)
    where
  functor := (boundedFlatAffineSupportedSectionNormalizedEquivalence j).functor
  exact := boundedFlatAffineSupportedSectionNormalizedEquivalence_exact j
  zero := Quillen.rebaseFunctor_obj_base _ _ _ _

/-- The specified normalization, rather than an equality of independently chosen zeros,
identifies the original evaluation functor with the actual Model arrow. -/
def boundedFlatAffineSupportedSectionEvaluationModelIso :
    boundedFlatAffineSupportedEvaluation j ⋙ AsSmall.up ≅
      (boundedFlatAffineSupportedSectionEvaluationModelMap j).functor := by
  refine ?_ ≪≫ boundedFlatAffineSupportedSectionEvaluationNormalizationIso j
  change boundedFlatAffineSupportedEvaluation j ⋙ AsSmall.up ≅
    (boundedFlatAffineSupportedSectionEquivalence j).functor ⋙ AsSmall.up
  rw [boundedFlatAffineSupportedSectionEquivalence_functor]

/-- The actual iterated-S map of the specified normalized evaluation Model arrow. -/
def boundedFlatAffineSupportedSectionEvaluationPrespectrumMap :
    prespectrum (boundedFlatAffineSupportedSectionModel j) ⟶
      originalPrespectrum (boundedFlatPerfectSupportedWaldhausen j) :=
  prespectrumMap (boundedFlatAffineSupportedSectionEvaluationModelMap j)

end Quillen.PerfectComplexes
