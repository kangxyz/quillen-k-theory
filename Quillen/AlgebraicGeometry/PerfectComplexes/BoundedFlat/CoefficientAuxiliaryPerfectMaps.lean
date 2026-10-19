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

/-- Evaluation of the original auxiliary enlargement is the original supported inclusion. -/
theorem auxiliaryFiberSectionKEquiv_enlargement (a : Under R) (n : ℕ)
    (x : (boundedFlatCoefficientSupportedFiberModel f T a).waldhausen.K n) :
    boundedFlatCoefficientSupportedSectionKEquiv (boundedFlatCoefficientSupportOpen Q T a).ι n
        (KMap (boundedFlatCoefficientSupportedFiberForgetModelMap f T a).exact n x) =
      boundedFlatPerfectSupportedUnionKMap (schemeMap f a)
        (boundedFlatCoefficientSupportOpen Q T a) n
        (boundedFlatCoefficientSupportedSectionKEquiv
          (boundedFlatCoefficientFiberSupportOpen f T a).ι n x) := by
  exact boundedFlatCoefficientEvaluationKEquiv_natural
    (boundedFlatCoefficientSupportedSectionWaldhausen
      (boundedFlatCoefficientFiberSupportOpen f T a).ι)
    (boundedFlatPerfectSupportedWaldhausen (boundedFlatCoefficientFiberSupportOpen f T a).ι)
    (boundedFlatCoefficientSupportedSectionEquivalence
      (boundedFlatCoefficientFiberSupportOpen f T a).ι)
    (boundedFlatCoefficientSupportedSectionEquivalence_functor_exact
      (boundedFlatCoefficientFiberSupportOpen f T a).ι)
    (boundedFlatCoefficientSupportedSectionEquivalence_inverse_exact
      (boundedFlatCoefficientFiberSupportOpen f T a).ι)
    (boundedFlatCoefficientSupportedSectionWaldhausen (boundedFlatCoefficientSupportOpen Q T a).ι)
    (boundedFlatPerfectSupportedWaldhausen (boundedFlatCoefficientSupportOpen Q T a).ι)
    (boundedFlatCoefficientSupportedSectionEquivalence (boundedFlatCoefficientSupportOpen Q T a).ι)
    (boundedFlatCoefficientSupportedSectionEquivalence_functor_exact
      (boundedFlatCoefficientSupportOpen Q T a).ι)
    (boundedFlatCoefficientSupportedSectionEquivalence_inverse_exact
      (boundedFlatCoefficientSupportOpen Q T a).ι)
    (boundedFlatCoefficientSupportedFiberForgetModelMap f T a).exact
    (subcategoryInclusion_exact _ _ (fun K h =>
      ((boundedFlatPerfectSupported_sup_opensRange_iff (schemeMap f a)
        (boundedFlatCoefficientSupportOpen Q T a) K).mp h).1))
    (by
      simp only [boundedFlatCoefficientSupportedSectionEquivalence_functor]
      exact eqToIso (boundedFlatCoefficientSupportedFiberEvaluation_forget f T a).symm) n x

/-- The original perfect supported inclusion commutes with the actual auxiliary row enlargement. -/
theorem auxiliaryPerfectKEquiv_enlargement [CompactSpace Q.left] (a : Under R) (n : ℕ)
    (x : (boundedFlatCoefficientSupportedFiberModel f T a).waldhausen.K n) :
    auxiliaryAmbientPerfectKEquiv T a n
        (KMap (boundedFlatCoefficientSupportedFiberForgetModelMap f T a).exact n x) =
      perfectSupportedUnionKMap (schemeMap f a) (boundedFlatCoefficientSupportOpen Q T a) n
        (auxiliaryFiberPerfectKEquiv f T a n x) := by
  let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
  change boundedFlatPerfectSupportedToPerfectSupportedKMap _ n
    (boundedFlatCoefficientSupportedSectionKEquiv _ n _) =
      perfectSupportedUnionKMap _ _ n
        (boundedFlatPerfectSupportedToPerfectSupportedKMap _ n
          (boundedFlatCoefficientSupportedSectionKEquiv _ n x))
  rw [auxiliaryFiberSectionKEquiv_enlargement]
  have h : (boundedFlatPerfectSupportedToPerfectSupportedKMap
      (boundedFlatCoefficientSupportOpen Q T a).ι n).comp
        (boundedFlatPerfectSupportedUnionKMap (schemeMap f a)
          (boundedFlatCoefficientSupportOpen Q T a) n) =
      (perfectSupportedUnionKMap (schemeMap f a)
        (boundedFlatCoefficientSupportOpen Q T a) n).comp
        (boundedFlatPerfectSupportedToPerfectSupportedKMap
          (boundedFlatCoefficientFiberSupportOpen f T a).ι n) := by
    unfold boundedFlatPerfectSupportedToPerfectSupportedKMap
      boundedFlatPerfectSupportedUnionKMap perfectSupportedUnionKMap subcategoryKMap
    rw [KMap_comp_KMap, KMap_comp_KMap]
  exact DFunLike.congr_fun h _

end Quillen.PerfectComplexes
