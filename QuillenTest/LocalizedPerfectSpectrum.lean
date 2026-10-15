/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.DerivedPullback

/-! Whole homotopies, actual inverses, arbitrary qc pullback and original K0
normalization in the constructed spectrum localization. -/
@[expose] public section


noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS Quillen.PerfectComplexes
universe u v
namespace QuillenTest.LocalizedPerfectSpectrum

open Quillen

/-- A specified whole coherent homotopy identifies the actual localized arrows. -/
theorem whole_homotopy_equality {E F : LoopPrespectrum.{u}} {f g : E ⟶ F}
    (H : Homotopy f g) : toStableLocalization.map f = toStableLocalization.map g :=
  toStableLocalization_map_eq_of_homotopy H

/-- The actual original stable equivalence has both inverse identities. -/
theorem original_inverse_laws {E F : LoopPrespectrum.{u}} (f : E ⟶ F) (h : IsStableEquivalence f) :
    toStableLocalization.map f ≫ (stableLocalizationIso f h).inv = 𝟙 _ ∧
      (stableLocalizationIso f h).inv ≫ toStableLocalization.map f = 𝟙 _ :=
  ⟨(stableLocalizationIso f h).hom_inv_id,(stableLocalizationIso f h).inv_hom_id⟩

/-- No additional original map becomes invertible without its actual stable test. -/
theorem original_iso_detection {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    (h : IsIso (toStableLocalization.map f)) (d : ℤ) :
    IsIso ((stableHomotopyFunctor d).map f) :=
  (toStableLocalization_isIso_iff f).mp h d

/-- The genuine universal lift agrees with the original functor on objects and maps. -/
theorem universal_factorization {D : Type v} [Category D] (T : LoopPrespectrum.{u} ⥤ D)
    (hH : ∀ {E F : LoopPrespectrum.{u}} {f g : E ⟶ F}, Homotopy f g → T.map f = T.map g)
    (hW : ∀ {E F : LoopPrespectrum.{u}} (f : E ⟶ F), IsStableEquivalence f → IsIso (T.map f)) :
    toStableLocalization ⋙ stableLocalizationLift T hH hW = T :=
  toStableLocalization_comp_lift T hH hW

/-- The actual bounded-flat model works functorially before imposing qc. -/
theorem bounded_flat_all_schemes {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    boundedFlatLocalizedPullback (f ≫ g) = boundedFlatLocalizedPullback g ≫
      boundedFlatLocalizedPullback f :=
  boundedFlatLocalizedPullback_comp f g

/-- Actual arbitrary qc scheme maps compose without any flat or finite-Tor premise. -/
theorem arbitrary_derived_composition {X Y Z : Scheme.{u}}
    [CompactSpace X] [CompactSpace Y] [CompactSpace Z] (f : X ⟶ Y) (g : Y ⟶ Z) :
    perfectLocalizedPullback (f ≫ g) = perfectLocalizedPullback g ≫ perfectLocalizedPullback f :=
  perfectLocalizedPullback_comp f g

/-- The original representative square uniquely fixes the derived spectrum morphism. -/
theorem unique_original_representative_map {X Y : Scheme.{u}} [CompactSpace X] [CompactSpace Y]
    (f : X ⟶ Y) (a b : perfectLocalizedSpectrum Y ⟶ perfectLocalizedSpectrum X)
    (ha : (boundedFlatPerfectSpectrumIso Y).hom ≫ a =
      boundedFlatLocalizedPullback f ≫ (boundedFlatPerfectSpectrumIso X).hom)
    (hb : (boundedFlatPerfectSpectrumIso Y).hom ≫ b =
      boundedFlatLocalizedPullback f ≫ (boundedFlatPerfectSpectrumIso X).hom) : a = b :=
  (perfectLocalizedPullback_unique f a ha).trans (perfectLocalizedPullback_unique f b hb).symm

/-- At degree zero the unchanged original perfect K-map and group law are recovered. -/
theorem original_kzero_map {X Y : Scheme.{u}} [CompactSpace X] [CompactSpace Y]
    (f : X ⟶ Y) (a : PerfectK Y 0) :
    originalKStableEquiv (perfectWaldhausen X) 0 (Additive.ofMul (perfectKPullback f 0 a)) =
      (localizedStableHomotopyFunctor ((0 : ℕ) : ℤ)).map (perfectLocalizedPullback f)
        (originalKStableEquiv (perfectWaldhausen Y) 0 (Additive.ofMul a)) :=
  perfectLocalizedPullback_originalK_naturality f 0 a

/-- Exact flat pullback agrees as an actual spectrum morphism, not just on K-groups. -/
theorem original_flat_spectrum_map {X Y : Scheme.{u}} [CompactSpace X] [CompactSpace Y]
    (f : X ⟶ Y) [Flat f] :
    perfectLocalizedPullback f = localizedSpectrumMap _ _ (perfectFlatPullback_waldhausenExact f) :=
  perfectLocalizedPullback_eq_flat f

/-- The natural model comparison has the original inclusion as its forward arrow. -/
theorem actual_inclusion_component (X : AlgebraicGeometry.Scheme.QuasiCompactSchemes.{u}) :
    boundedFlatPerfectSpectrumNatIso.hom.app (Opposite.op X) =
      localizedSpectrumMap _ _ (boundedFlatPerfectInclusion_exact X.obj) := rfl

end QuillenTest.LocalizedPerfectSpectrum
