/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientAuxiliaryPerfectClasses
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedFiberLocalizationModels

/-! # Original auxiliary support enlargement on perfect supported classes -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.Waldhausen
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)

omit [IsOpenImmersion f.left] in
/-- The genuine supported evaluation square retains the original geometric restriction K-map. -/
theorem auxiliarySectionKEquiv_restriction (a : Under R) (n : ℕ)
    (x : (boundedFlatCoefficientSupportedSectionWaldhausen
      (boundedFlatCoefficientSupportOpen Q T a).ι).K n) :
    boundedFlatCoefficientSupportedSectionKEquiv (boundedFlatCoefficientOpenSupportOpen f T a).ι n
        (KMap (boundedFlatCoefficientSupportedOpenRestriction_fine_exact f T a) n x) =
      KMap (boundedFlatPerfectSupportedPullback_exact
        (supportRestrictionPair (schemeMap f a) (boundedFlatCoefficientSupportOpen Q T a))) n
        (boundedFlatCoefficientSupportedSectionKEquiv
          (boundedFlatCoefficientSupportOpen Q T a).ι n x) :=
  boundedFlatCoefficientEvaluationKEquiv_natural
    (boundedFlatCoefficientSupportedSectionWaldhausen (boundedFlatCoefficientSupportOpen Q T a).ι)
    (boundedFlatPerfectSupportedWaldhausen (boundedFlatCoefficientSupportOpen Q T a).ι)
    (boundedFlatCoefficientSupportedSectionEquivalence (boundedFlatCoefficientSupportOpen Q T a).ι)
    (boundedFlatCoefficientSupportedSectionEquivalence_functor_exact
      (boundedFlatCoefficientSupportOpen Q T a).ι)
    (boundedFlatCoefficientSupportedSectionEquivalence_inverse_exact
      (boundedFlatCoefficientSupportOpen Q T a).ι)
    (boundedFlatCoefficientSupportedSectionWaldhausen
      (boundedFlatCoefficientOpenSupportOpen f T a).ι)
    (boundedFlatPerfectSupportedWaldhausen (boundedFlatCoefficientOpenSupportOpen f T a).ι)
    (boundedFlatCoefficientSupportedSectionEquivalence
      (boundedFlatCoefficientOpenSupportOpen f T a).ι)
    (boundedFlatCoefficientSupportedSectionEquivalence_functor_exact
      (boundedFlatCoefficientOpenSupportOpen f T a).ι)
    (boundedFlatCoefficientSupportedSectionEquivalence_inverse_exact
      (boundedFlatCoefficientOpenSupportOpen f T a).ι)
    (boundedFlatCoefficientSupportedOpenRestriction_fine_exact f T a)
    (boundedFlatPerfectSupportedPullback_exact
      (supportRestrictionPair (schemeMap f a) (boundedFlatCoefficientSupportOpen Q T a)))
    (by
      simp only [boundedFlatCoefficientSupportedSectionEquivalence_functor]
      exact boundedFlatCoefficientSupportedOpenRestrictionEvaluationIso f T a) n x

/-- The original fine geometric restriction is preserved, without a new coarse comparison. -/
theorem auxiliaryPerfectKEquiv_restriction [CompactSpace P.left] [CompactSpace Q.left]
    (a : Under R) (n : ℕ)
    (x : (boundedFlatCoefficientSupportedAmbientModel T a).waldhausen.K n) :
    auxiliaryOpenPerfectKEquiv f T a n
        (KMap (boundedFlatCoefficientSupportedOpenRestriction_fine_exact f T a) n x) =
      perfectSupportedKRestrict (schemeMap f a) (boundedFlatCoefficientSupportOpen Q T a) n
        (auxiliaryAmbientPerfectKEquiv T a n x) := by
  let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
  let : CompactSpace (space (op P, a)) := compactSpace_space (op P, a)
  change boundedFlatPerfectSupportedToPerfectSupportedKMap _ n
    (boundedFlatCoefficientSupportedSectionKEquiv _ n _) =
      perfectSupportedKRestrict _ _ n
        (boundedFlatPerfectSupportedToPerfectSupportedKMap _ n
          (boundedFlatCoefficientSupportedSectionKEquiv _ n x))
  have he := auxiliarySectionKEquiv_restriction f T a n x
  have h : (boundedFlatPerfectSupportedToPerfectSupportedKMap
      (boundedFlatCoefficientOpenSupportOpen f T a).ι n).comp
        (KMap (boundedFlatPerfectSupportedPullback_exact
          (supportRestrictionPair (schemeMap f a) (boundedFlatCoefficientSupportOpen Q T a))) n) =
      (perfectSupportedKRestrict (schemeMap f a) (boundedFlatCoefficientSupportOpen Q T a) n).comp
        (boundedFlatPerfectSupportedToPerfectSupportedKMap
          (boundedFlatCoefficientSupportOpen Q T a).ι n) := by
    unfold boundedFlatPerfectSupportedToPerfectSupportedKMap perfectSupportedKRestrict
    rw [KMap_comp_KMap, KMap_comp_KMap]
    exact KMap_eq_of_iso _ _ (boundedFlatPerfectSupportedOriginalRestrictionIso
      (schemeMap f a) (boundedFlatCoefficientSupportOpen Q T a)).symm n
  exact (congrArg (boundedFlatPerfectSupportedToPerfectSupportedKMap
    (boundedFlatCoefficientOpenSupportOpen f T a).ι n) he).trans (DFunLike.congr_fun h _)

end Quillen.PerfectComplexes
