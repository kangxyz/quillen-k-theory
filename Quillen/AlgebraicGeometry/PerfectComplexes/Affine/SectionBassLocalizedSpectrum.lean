/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionLocalizedComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassTelescope

/-!
# The original perfect spectrum maps naturally to the actual Bass telescope

The unchanged initial section inclusion is transported through the proved original evaluation
and bounded-flat inclusion isomorphisms. This constructs an actual natural map from original
perfect affine spectra to the stable-localization image of the actual Bass telescope. All
coefficient maps and signed stable groups retain their original definitions and universes.

The codomain is the constructed Bass telescope. This map does not assert a classical negative
Bass group identification, stable cofiber exactness or a nonconnective localization theorem.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes

/-- The actual original Bass telescope, with its strict coefficient maps, in the localization. -/
def boundedFlatAffineSectionBassLocalizedSpectrumFunctor :
    CommRingCat.{u} ⥤ StableLocalization.{u+1} :=
  boundedFlatAffineSectionBassTelescopeFunctor ⋙ toStableLocalization

/-- The original initial section inclusion after the existing stable localization functor. -/
def boundedFlatAffineSectionBassLocalizedInitial :
    boundedFlatAffineSectionLocalizedSpectrumFunctor.{u} ⟶
      boundedFlatAffineSectionBassLocalizedSpectrumFunctor :=
  Functor.whiskerRight boundedFlatAffineSectionBassTelescopeInitial toStableLocalization

/-- The unchanged perfect spectrum maps naturally to the actual section Bass telescope. -/
def affinePerfectBassTelescopeInitial :
    affinePerfectLocalizedSpectrumFunctor.{u} ⟶
      boundedFlatAffineSectionBassLocalizedSpectrumFunctor :=
  boundedFlatAffineSectionPerfectLocalizedNatIso.inv ≫
    boundedFlatAffineSectionBassLocalizedInitial

/-- The actual initial map out of the original perfect spectrum at a coefficient ring. -/
def affinePerfectBassTelescopeInitialMap (R : CommRingCat.{u}) :
    perfectLocalizedSpectrum (Spec R) ⟶
      toStableLocalization.obj (boundedFlatAffineSectionBassTelescope R) :=
  affinePerfectBassTelescopeInitial.app R

/-- The formula retains the original inclusion inverse, actual evaluation inverse and stage zero. -/
theorem affinePerfectBassTelescopeInitialMap_eq (R : CommRingCat.{u}) :
    affinePerfectBassTelescopeInitialMap R =
      (boundedFlatPerfectSpectrumIso (Spec R)).inv ≫
        toStableLocalization.map (boundedFlatAffineSectionEvaluationInversePrespectrumMap R ≫
          boundedFlatAffineSectionBassTelescopeInitial.app R) := by
  change boundedFlatAffineSectionPerfectLocalizedNatIso.inv.app R ≫
    toStableLocalization.map (boundedFlatAffineSectionBassTelescopeInitial.app R) = _
  rw [boundedFlatAffineSectionPerfectLocalizedNatIso_inv_app, Functor.map_comp, Category.assoc]

/-- Original evaluation and inclusion recover exactly the original telescope initial face. -/
@[reassoc] theorem affinePerfectBassTelescopeInitialMap_representatives (R : CommRingCat.{u}) :
    toStableLocalization.map (boundedFlatAffineSectionEvaluationPrespectrumMap R) ≫
        (boundedFlatPerfectSpectrumIso (Spec R)).hom ≫ affinePerfectBassTelescopeInitialMap R =
      toStableLocalization.map (boundedFlatAffineSectionBassTelescopeInitial.app R) := by
  have h := congrArg (fun a ↦ a.app R)
    (Iso.hom_inv_id_assoc boundedFlatAffineSectionPerfectLocalizedNatIso
      boundedFlatAffineSectionBassLocalizedInitial)
  simpa only [affinePerfectBassTelescopeInitialMap, affinePerfectBassTelescopeInitial,
    boundedFlatAffineSectionBassLocalizedInitial, Functor.whiskerRight_app, NatTrans.comp_app,
    boundedFlatAffineSectionPerfectLocalizedNatIso_hom_app, Category.assoc] using h

/-- Every original derived coefficient pullback commutes with this actual initial map. -/
@[reassoc] theorem affinePerfectBassTelescopeInitialMap_naturality
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    perfectLocalizedPullback (Spec.map f) ≫ affinePerfectBassTelescopeInitialMap S =
      affinePerfectBassTelescopeInitialMap R ≫
        toStableLocalization.map (boundedFlatAffineSectionBassTelescopeMap f) :=
  affinePerfectBassTelescopeInitial.naturality f

/-- Every signed stable map is the same original inverse-and-initial-stage composite. -/
theorem affinePerfectBassTelescopeInitialMap_stable (R : CommRingCat.{u}) (d : ℤ) :
    (localizedStableHomotopyFunctor d).map (affinePerfectBassTelescopeInitialMap R) =
      (localizedStableHomotopyFunctor d).map (boundedFlatPerfectSpectrumIso (Spec R)).inv ≫
        (stableHomotopyFunctor d).map
          (boundedFlatAffineSectionEvaluationInversePrespectrumMap R) ≫
        (stableHomotopyFunctor d).map (boundedFlatAffineSectionBassTelescopeInitial.app R) := by
  rw [affinePerfectBassTelescopeInitialMap_eq, Functor.map_comp,
    localizedStableHomotopyFunctor_original_map, Functor.map_comp]

/-- The induced nonnegative map retains the unchanged original perfect K-map on every coefficient.
-/
theorem affinePerfectBassTelescopeInitialMap_originalK_naturality
    {R S : CommRingCat.{u}} (f : R ⟶ S) (n : ℕ) (a : PerfectK (Spec R) n) :
    (localizedStableHomotopyFunctor (n : ℤ)).map (affinePerfectBassTelescopeInitialMap S)
        (Waldhausen.IteratedS.originalKStableEquiv (perfectWaldhausen (Spec S)) n
          (Additive.ofMul (perfectKPullback (Spec.map f) n a))) =
      (stableHomotopyFunctor (n : ℤ)).map (boundedFlatAffineSectionBassTelescopeMap f)
        ((localizedStableHomotopyFunctor (n : ℤ)).map (affinePerfectBassTelescopeInitialMap R)
          (Waldhausen.IteratedS.originalKStableEquiv (perfectWaldhausen (Spec R)) n
            (Additive.ofMul a))) := by
  have h := congrArg ((localizedStableHomotopyFunctor (n : ℤ)).map)
    (affinePerfectBassTelescopeInitialMap_naturality f)
  rw [Functor.map_comp, Functor.map_comp, localizedStableHomotopyFunctor_original_map] at h
  exact (congrArg
    ((localizedStableHomotopyFunctor (n : ℤ)).map (affinePerfectBassTelescopeInitialMap S))
    (perfectLocalizedPullback_originalK_naturality (Spec.map f) n a)).trans
      (ConcreteCategory.congr_hom h
        (Waldhausen.IteratedS.originalKStableEquiv (perfectWaldhausen (Spec R)) n
          (Additive.ofMul a)))

end Quillen.PerfectComplexes
