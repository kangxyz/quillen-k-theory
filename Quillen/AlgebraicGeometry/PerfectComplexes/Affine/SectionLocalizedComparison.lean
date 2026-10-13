/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.LocalizedSpectrum
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionSpectrumEquivalence
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionSpectrumNaturality

/-!
# Original section evaluation in the stable localization

The unchanged section evaluation map gives a natural isomorphism to the original bounded-flat
geometric spectrum. Naturality is the image of the proved whole coefficient track. Its inverse
is the image of the actual normalized homotopy inverse, and composition with the original
bounded-flat inclusion gives the comparison with original perfect spectra.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes

/-- The unchanged section prespectrum followed by the existing stable localization functor. -/
def boundedFlatAffineSectionLocalizedSpectrumFunctor :
    CommRingCat.{u} ⥤ StableLocalization.{u+1} :=
  boundedFlatAffineSectionPrespectrumFunctor ⋙ toStableLocalization

/-- Original evaluation, inverted using its proved actual stable equivalence. -/
def boundedFlatAffineSectionEvaluationLocalizedIso (R : CommRingCat.{u}) :
    toStableLocalization.obj (boundedFlatAffineSectionPrespectrumFunctor.obj R) ≅
      boundedFlatLocalizedSpectrum (Spec R) :=
  stableLocalizationIso (boundedFlatAffineSectionEvaluationPrespectrumMap R)
    (boundedFlatAffineSectionEvaluation_isStableEquivalence R)

/-- The comparison retains the unchanged original forward evaluation map. -/
@[simp] theorem boundedFlatAffineSectionEvaluationLocalizedIso_hom (R : CommRingCat.{u}) :
    (boundedFlatAffineSectionEvaluationLocalizedIso R).hom =
      toStableLocalization.map (boundedFlatAffineSectionEvaluationPrespectrumMap R) := rfl

/-- The inverse is the image of the actual previously constructed normalized inverse map. -/
theorem boundedFlatAffineSectionEvaluationLocalizedIso_inv (R : CommRingCat.{u}) :
    (boundedFlatAffineSectionEvaluationLocalizedIso R).inv =
      toStableLocalization.map (boundedFlatAffineSectionEvaluationInversePrespectrumMap R) := by
  apply (cancel_mono (boundedFlatAffineSectionEvaluationLocalizedIso R).hom).mp
  rw [Iso.inv_hom_id, boundedFlatAffineSectionEvaluationLocalizedIso_hom,
    ← Functor.map_comp,
    toStableLocalization_map_eq_of_homotopy
      (boundedFlatAffineSectionEvaluationRightHomotopy R), CategoryTheory.Functor.map_id]

/-- The whole original coefficient track proves actual localized naturality of evaluation. -/
theorem boundedFlatAffineSectionEvaluationLocalizedIso_naturality
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    toStableLocalization.map (boundedFlatAffineSectionPrespectrumFunctor.map f) ≫
        (boundedFlatAffineSectionEvaluationLocalizedIso S).hom =
      (boundedFlatAffineSectionEvaluationLocalizedIso R).hom ≫
        boundedFlatLocalizedPullback (Spec.map f) := by
  change toStableLocalization.map (boundedFlatAffineSectionPrespectrumFunctor.map f) ≫
      toStableLocalization.map (boundedFlatAffineSectionEvaluationPrespectrumMap S) =
    toStableLocalization.map (boundedFlatAffineSectionEvaluationPrespectrumMap R) ≫
      toStableLocalization.map (boundedFlatPerfectPrespectrumMap (Spec.map f))
  have h := toStableLocalization_map_eq_of_homotopy
    (boundedFlatAffineSectionEvaluationCoefficientHomotopy f)
  simpa only [Functor.map_comp] using h

/-- Actual coefficient restriction and original geometric pullback have the natural evaluation iso.
-/
def boundedFlatAffineSectionEvaluationLocalizedNatIso :
    boundedFlatAffineSectionLocalizedSpectrumFunctor.{u} ≅
      affineBoundedFlatLocalizedSpectrumFunctor :=
  NatIso.ofComponents boundedFlatAffineSectionEvaluationLocalizedIso
    boundedFlatAffineSectionEvaluationLocalizedIso_naturality

/-- Every component is exactly the original evaluation comparison, not a newly selected iso. -/
@[simp] theorem boundedFlatAffineSectionEvaluationLocalizedNatIso_hom_app
    (R : CommRingCat.{u}) :
    boundedFlatAffineSectionEvaluationLocalizedNatIso.hom.app R =
      toStableLocalization.map (boundedFlatAffineSectionEvaluationPrespectrumMap R) := rfl

/-- Evaluation followed by the original bounded-flat inclusion compares perfect spectra. -/
def boundedFlatAffineSectionPerfectLocalizedNatIso :
    boundedFlatAffineSectionLocalizedSpectrumFunctor.{u} ≅ affinePerfectLocalizedSpectrumFunctor :=
  boundedFlatAffineSectionEvaluationLocalizedNatIso ≪≫ affineBoundedFlatPerfectSpectrumNatIso

/-- The forward comparison uses exactly the two original maps. -/
@[simp] theorem boundedFlatAffineSectionPerfectLocalizedNatIso_hom_app (R : CommRingCat.{u}) :
    boundedFlatAffineSectionPerfectLocalizedNatIso.hom.app R =
      toStableLocalization.map (boundedFlatAffineSectionEvaluationPrespectrumMap R) ≫
        (boundedFlatPerfectSpectrumIso (Spec R)).hom := rfl

/-- The inverse retains the actual evaluation inverse and the original localized inclusion inverse.
-/
theorem boundedFlatAffineSectionPerfectLocalizedNatIso_inv_app (R : CommRingCat.{u}) :
    boundedFlatAffineSectionPerfectLocalizedNatIso.inv.app R =
      (boundedFlatPerfectSpectrumIso (Spec R)).inv ≫
        toStableLocalization.map (boundedFlatAffineSectionEvaluationInversePrespectrumMap R) := by
  change (boundedFlatPerfectSpectrumIso (Spec R)).inv ≫
    (boundedFlatAffineSectionEvaluationLocalizedIso R).inv = _
  rw [boundedFlatAffineSectionEvaluationLocalizedIso_inv]

end Quillen.PerfectComplexes
