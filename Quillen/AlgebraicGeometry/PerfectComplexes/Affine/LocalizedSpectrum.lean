/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.DerivedPullback

/-!
# Original affine perfect spectra and their actual localized coefficient maps

The existing bounded-flat and perfect localized spectrum functors restrict to coefficient
rings using the literal `Spec.map` arrows. Their natural comparison retains the original
bounded-flat inclusion, inverted only in the previously constructed stable localization.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes

/-- The unchanged bounded-flat geometric spectra with their original coefficient pullbacks. -/
def affineBoundedFlatLocalizedSpectrumFunctor : CommRingCat.{u} ⥤ StableLocalization.{u+1} where
  obj R := boundedFlatLocalizedSpectrum (Spec R)
  map f := boundedFlatLocalizedPullback (Spec.map f)
  map_id R := by rw [Spec.map_id, boundedFlatLocalizedPullback_id]
  map_comp f g := by rw [Spec.map_comp, boundedFlatLocalizedPullback_comp]

/-- The original perfect affine spectra and their already constructed derived pullbacks. -/
def affinePerfectLocalizedSpectrumFunctor : CommRingCat.{u} ⥤ StableLocalization.{u+1} where
  obj R := perfectLocalizedSpectrum (Spec R)
  map f := perfectLocalizedPullback (Spec.map f)
  map_id R := by rw [Spec.map_id, perfectLocalizedPullback_id]
  map_comp f g := by rw [Spec.map_comp, perfectLocalizedPullback_comp]

/-- The actual original inclusion supplies the natural isomorphism on affine coefficient rings. -/
def affineBoundedFlatPerfectSpectrumNatIso :
    affineBoundedFlatLocalizedSpectrumFunctor.{u} ≅ affinePerfectLocalizedSpectrumFunctor :=
  NatIso.ofComponents (fun R ↦ boundedFlatPerfectSpectrumIso (Spec R))
    (fun f ↦ (perfectLocalizedPullback_representatives (Spec.map f)).symm)

/-- Every comparison component is the original bounded-flat inclusion in the localization. -/
@[simp] theorem affineBoundedFlatPerfectSpectrumNatIso_hom_app (R : CommRingCat.{u}) :
    affineBoundedFlatPerfectSpectrumNatIso.hom.app R =
      (boundedFlatPerfectSpectrumIso (Spec R)).hom := rfl

end Quillen.PerfectComplexes
