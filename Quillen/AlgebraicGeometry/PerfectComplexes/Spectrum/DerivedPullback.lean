/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.SConstruction.Iterated.LocalizedFunctoriality
public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedPullbackFunctor

/-!
Arbitrary derived pullback of original perfect spectra on qc schemes in the constructed stable
localization. The actual bounded-flat inclusion is inverted via its proved stable equivalence; flat
maps and original K-groups are retained.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes

/-- The image of the bounded-flat perfect prespectrum in the stable localization. -/
abbrev boundedFlatLocalizedSpectrum (X : Scheme.{u}) : StableLocalization.{u+1} :=
  localizedSpectrum (boundedFlatPerfectWaldhausen X)

/-- The image of the perfect prespectrum in the stable localization. -/
abbrev perfectLocalizedSpectrum (X : Scheme.{u}) : StableLocalization.{u+1} :=
  localizedSpectrum (perfectWaldhausen X)

/-- The morphism in the stable localization induced by bounded-flat pullback. -/
def boundedFlatLocalizedPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    boundedFlatLocalizedSpectrum Y ⟶ boundedFlatLocalizedSpectrum X :=
  localizedSpectrumMap _ _ (boundedFlatPerfectPullback_exact f)

@[simp] theorem boundedFlatLocalizedPullback_id (X : Scheme.{u}) :
    boundedFlatLocalizedPullback (𝟙 X) = 𝟙 _ :=
  (localizedSpectrumMap_iso _ _ (boundedFlatPerfectPullback_exact (𝟙 X))
    (Waldhausen.IsExact.id _ _) (boundedFlatPerfectPullbackIdIso X)).trans (localizedSpectrumMap_id
      _)

@[simp] theorem boundedFlatLocalizedPullback_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    boundedFlatLocalizedPullback (f ≫ g) = boundedFlatLocalizedPullback g ≫
      boundedFlatLocalizedPullback f :=
  (localizedSpectrumMap_iso _ _ (boundedFlatPerfectPullback_exact (f ≫ g))
    ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f))
    (boundedFlatPerfectPullbackCompIso f g)).trans (localizedSpectrumMap_comp _ _ _ _ _)

/-- The actual bounded-flat enhanced geometric pullback is a contravariant functor. -/
def BoundedFlatLocalizedSpectrumFunctor : Scheme.{u}ᵒᵖ ⥤ StableLocalization.{u+1} where
  obj X := boundedFlatLocalizedSpectrum X.unop
  map f := boundedFlatLocalizedPullback f.unop
  map_id X := boundedFlatLocalizedPullback_id X.unop
  map_comp f g := boundedFlatLocalizedPullback_comp g.unop f.unop

/-- The literal inclusion is inverted only after its actual all-degree K-equivalence was proved. -/
def boundedFlatPerfectSpectrumIso (X : Scheme.{u}) [CompactSpace X] :
    boundedFlatLocalizedSpectrum X ≅ perfectLocalizedSpectrum X :=
  localizedSpectrumMapIso _ _ (boundedFlatPerfectInclusion_exact X)
    (boundedFlatPerfectToPerfectKMap_bijective X)

@[simp] theorem boundedFlatPerfectSpectrumIso_hom (X : Scheme.{u}) [CompactSpace X] :
    (boundedFlatPerfectSpectrumIso X).hom =
      localizedSpectrumMap _ _ (boundedFlatPerfectInclusion_exact X) := rfl

/-- Arbitrary derived pullback as a genuine morphism between original perfect
spectra in the constructed localization. Both ambient schemes are qc. -/
def perfectLocalizedPullback {X Y : Scheme.{u}} [CompactSpace X] [CompactSpace Y]
    (f : X ⟶ Y) : perfectLocalizedSpectrum Y ⟶ perfectLocalizedSpectrum X :=
  (boundedFlatPerfectSpectrumIso Y).inv ≫ boundedFlatLocalizedPullback f ≫
    (boundedFlatPerfectSpectrumIso X).hom

@[reassoc] theorem perfectLocalizedPullback_representatives {X Y : Scheme.{u}}
    [CompactSpace X] [CompactSpace Y] (f : X ⟶ Y) :
    (boundedFlatPerfectSpectrumIso Y).hom ≫ perfectLocalizedPullback f =
      boundedFlatLocalizedPullback f ≫ (boundedFlatPerfectSpectrumIso X).hom := by
  simp only [perfectLocalizedPullback, Iso.hom_inv_id_assoc]

theorem perfectLocalizedPullback_unique {X Y : Scheme.{u}}
    [CompactSpace X] [CompactSpace Y] (f : X ⟶ Y)
    (a : perfectLocalizedSpectrum Y ⟶ perfectLocalizedSpectrum X)
    (ha : (boundedFlatPerfectSpectrumIso Y).hom ≫ a =
      boundedFlatLocalizedPullback f ≫ (boundedFlatPerfectSpectrumIso X).hom) :
    a = perfectLocalizedPullback f := by
  apply (cancel_epi (boundedFlatPerfectSpectrumIso Y).hom).mp
  exact ha.trans (perfectLocalizedPullback_representatives f).symm

@[simp] theorem perfectLocalizedPullback_id (X : Scheme.{u}) [CompactSpace X] :
    perfectLocalizedPullback (𝟙 X) = 𝟙 _ := by
  simp only [perfectLocalizedPullback, boundedFlatLocalizedPullback_id, Category.id_comp,
    Iso.inv_hom_id]

@[simp] theorem perfectLocalizedPullback_comp {X Y Z : Scheme.{u}}
    [CompactSpace X] [CompactSpace Y] [CompactSpace Z] (f : X ⟶ Y) (g : Y ⟶ Z) :
    perfectLocalizedPullback (f ≫ g) = perfectLocalizedPullback g ≫ perfectLocalizedPullback f := by
  simp only [perfectLocalizedPullback, boundedFlatLocalizedPullback_comp, Category.assoc,
    Iso.hom_inv_id_assoc]

/-- Original perfect spectra form an actual contravariant functor in the
constructed homotopy/stable localization; no strict continuous inverse is asserted. -/
def PerfectLocalizedSpectrumFunctor : Quillen.Scheme.QuasiCompactSchemes.{u}ᵒᵖ ⥤
  StableLocalization.{u+1} where
  obj X := perfectLocalizedSpectrum X.unop.obj
  map f := perfectLocalizedPullback f.unop.hom
  map_id X := perfectLocalizedPullback_id X.unop.obj
  map_comp f g := perfectLocalizedPullback_comp g.unop.hom f.unop.hom

/-- The literal bounded-flat inclusion is the forward component of an actual natural isomorphism. -/
def boundedFlatPerfectSpectrumNatIso :
    Quillen.Scheme.quasiCompactSchemesInclusion.op ⋙ BoundedFlatLocalizedSpectrumFunctor ≅
      PerfectLocalizedSpectrumFunctor :=
  NatIso.ofComponents (fun X ↦ boundedFlatPerfectSpectrumIso X.unop.obj)
    (fun f ↦ (perfectLocalizedPullback_representatives f.unop.hom).symm)

/-- On flat morphisms the actual original exact pullback spectrum map is retained. -/
theorem perfectLocalizedPullback_eq_flat {X Y : Scheme.{u}}
    [CompactSpace X] [CompactSpace Y] (f : X ⟶ Y) [Flat f] :
    perfectLocalizedPullback f = localizedSpectrumMap _ _ (perfectFlatPullback_waldhausenExact f) :=
      by
  symm
  apply perfectLocalizedPullback_unique
  change localizedSpectrumMap _ _ (boundedFlatPerfectInclusion_exact Y) ≫
    localizedSpectrumMap _ _ (perfectFlatPullback_waldhausenExact f) =
      localizedSpectrumMap _ _ (boundedFlatPerfectPullback_exact f) ≫
        localizedSpectrumMap _ _ (boundedFlatPerfectInclusion_exact X)
  rw [← localizedSpectrumMap_comp, ← localizedSpectrumMap_comp]

/-- In every nonnegative degree, the spectrum-level derived pullback is exactly
the previously defined original perfect K-map, including its K0 group law. -/
theorem perfectLocalizedPullback_originalK_naturality {X Y : Scheme.{u}}
    [CompactSpace X] [CompactSpace Y] (f : X ⟶ Y) (n : ℕ) (a : PerfectK Y n) :
    originalKStableEquiv (perfectWaldhausen X) n (Additive.ofMul (perfectKPullback f n a)) =
      (localizedStableHomotopyFunctor (n : ℤ)).map (perfectLocalizedPullback f)
        (originalKStableEquiv (perfectWaldhausen Y) n (Additive.ofMul a)) := by
  obtain ⟨b,rfl⟩ := (boundedFlatPerfectToPerfectKMap_bijective Y n).surjective a
  have hY := localizedSpectrumMap_originalK_naturality _ _ (boundedFlatPerfectInclusion_exact Y) n b
  have hX := localizedSpectrumMap_originalK_naturality _ _ (boundedFlatPerfectInclusion_exact X) n
    (boundedFlatPerfectKPullback f n b)
  have hF := localizedSpectrumMap_originalK_naturality _ _ (boundedFlatPerfectPullback_exact f) n b
  have hs := congrArg ((localizedStableHomotopyFunctor (n : ℤ)).map)
    (perfectLocalizedPullback_representatives f)
  rw [Functor.map_comp,Functor.map_comp] at hs
  have hp := DFunLike.congr_fun (perfectKPullback_comp_boundedFlat f n) b
  change perfectKPullback f n (boundedFlatPerfectToPerfectKMap Y n b) =
    boundedFlatPerfectToPerfectKMap X n (boundedFlatPerfectKPullback f n b) at hp
  rw [hp]
  exact hX.trans ((congrArg ((localizedStableHomotopyFunctor (n : ℤ)).map
    (boundedFlatPerfectSpectrumIso X).hom) hF).trans
      ((ConcreteCategory.congr_hom hs
        (originalKStableEquiv (boundedFlatPerfectWaldhausen Y) n (Additive.ofMul b))).symm.trans
        (congrArg ((localizedStableHomotopyFunctor (n : ℤ)).map (perfectLocalizedPullback f))
          hY.symm)))

end Quillen.PerfectComplexes
