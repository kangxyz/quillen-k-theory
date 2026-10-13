/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.FlatPullback

/-!
# Semantic consumers for actual flat coherent pullback

These consumers exercise arbitrary coherent-object pullback, exactness from
real ring-map flatness, preservation of the original G-theory restriction,
composition, and naturality of the original canonical K-to-G map.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace QuillenTest.CoherentFlatPullback

open Quillen

/-- Finite-presentation transport applies without flatness or noetherianity. -/
theorem arbitraryFinitePresentation {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) [M.IsFinitePresentation] :
    ((Scheme.Modules.pullback f).obj M).IsFinitePresentation := inferInstance

/-- Quasicoherence also transports independently of finiteness and flatness. -/
theorem arbitraryQuasicoherence {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pullback f).obj M).IsQuasicoherent := inferInstance

/-- Pullback of a coherent object is the original module-sheaf pullback,
even for a morphism that is not assumed flat. -/
theorem coherentUnderlyingSheaf {X Y : AlgebraicGeometry.Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    (M : CoherentScheme.FiniteTypeSheaves Y) :
    ((CoherentScheme.coherentPullback f).obj M).obj =
      (Scheme.Modules.pullback f).obj M.obj := rfl

/-- Actual flat ring maps preserve sheaf short exact sequences of
quasicoherent modules, with no noetherianity or finiteness assumption. -/
theorem affineExactness {R S : CommRingCat.{u}} (φ : R ⟶ S) (hφ : φ.hom.Flat)
    (C : ShortComplex (Spec R).Modules) (hC : C.ShortExact)
    [C.X₁.IsQuasicoherent] [C.X₂.IsQuasicoherent] :
    (C.map (Scheme.Modules.pullback (Spec.map φ))).ShortExact := by
  have : Flat (Spec.map φ) := Flat.SpecMap_iff.mpr hφ
  exact CoherentScheme.shortExact_pullback_of_flat (Spec.map φ) hC

/-- An actual flat ring map induces the canonical G-map between noetherian spectra. -/
def affineGMap {R S : CommRingCat.{u}} [IsNoetherianRing R] [IsNoetherianRing S]
    (φ : R ⟶ S) (hφ : φ.hom.Flat) (n : ℕ) :
    Quillen.Scheme.G (Spec R) n →* Quillen.Scheme.G (Spec S) n := by
  have : Flat (Spec.map φ) := Flat.SpecMap_iff.mpr hφ
  exact Quillen.Scheme.pullbackG (Spec.map φ) n

/-- Successive flat pullbacks compute the map of the actual composite. -/
theorem compositeGMap {X Y Z : AlgebraicGeometry.Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f] [Flat g] (n : ℕ)
    (x : Quillen.Scheme.G Z n) :
    Quillen.Scheme.pullbackG (f ≫ g) n x =
      Quillen.Scheme.pullbackG f n (Quillen.Scheme.pullbackG g n x) := by
  rw [Quillen.Scheme.pullbackG_comp]
  rfl

/-- The new flat G-map agrees with the already-existing open restriction. -/
theorem originalOpenRestriction {X Y : AlgebraicGeometry.Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (j : X ⟶ Y)
    [IsOpenImmersion j] (n : ℕ) :
    Quillen.Scheme.pullbackG j n = Quillen.Scheme.restrictG j n :=
  Quillen.Scheme.pullbackG_eq_restrictG j n

/-- The natural square uses the original public K, G and K-to-G maps. -/
theorem originalComparisonSquare {X Y : AlgebraicGeometry.Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y) [Flat f]
    (n : ℕ) (x : Quillen.Scheme.K Y n) :
    Quillen.Scheme.pullbackG f n (Quillen.Scheme.KToG Y n x) =
      Quillen.Scheme.KToG X n (Quillen.Scheme.pullbackK f n x) :=
  Quillen.Scheme.KToG_pullback_apply f n x

end QuillenTest.CoherentFlatPullback
