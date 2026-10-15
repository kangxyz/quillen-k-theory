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

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent


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
    (M : AlgebraicGeometry.Scheme.Modules.QuasiCoherent.FiniteTypeSheaves Y) :
    ((AlgebraicGeometry.Scheme.Modules.Coherent.coherentPullback f).obj M).obj =
      (Scheme.Modules.pullback f).obj M.obj := rfl

/-- Actual flat ring maps preserve sheaf short exact sequences of
quasicoherent modules, with no noetherianity or finiteness assumption. -/
theorem affineExactness {R S : CommRingCat.{u}} (φ : R ⟶ S) (hφ : φ.hom.Flat)
    (C : ShortComplex (Spec R).Modules) (hC : C.ShortExact)
    [C.X₁.IsQuasicoherent] [C.X₂.IsQuasicoherent] :
    (C.map (Scheme.Modules.pullback (Spec.map φ))).ShortExact := by
  have : Flat (Spec.map φ) := Flat.SpecMap_iff.mpr hφ
  exact AlgebraicGeometry.Scheme.Modules.QuasiCoherent.shortExact_pullback_of_flat (Spec.map φ) hC

/-- An actual flat ring map induces the canonical G-map between noetherian spectra. -/
def affineGMap {R S : CommRingCat.{u}} [IsNoetherianRing R] [IsNoetherianRing S]
    (φ : R ⟶ S) (hφ : φ.hom.Flat) (n : ℕ) :
    AlgebraicGeometry.Scheme.G (Spec R) n →* AlgebraicGeometry.Scheme.G (Spec S) n := by
  have : Flat (Spec.map φ) := Flat.SpecMap_iff.mpr hφ
  exact AlgebraicGeometry.Scheme.pullbackG (Spec.map φ) n

/-- Successive flat pullbacks compute the map of the actual composite. -/
theorem compositeGMap {X Y Z : AlgebraicGeometry.Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f] [Flat g] (n : ℕ)
    (x : AlgebraicGeometry.Scheme.G Z n) :
    AlgebraicGeometry.Scheme.pullbackG (f ≫ g) n x =
      AlgebraicGeometry.Scheme.pullbackG f n (AlgebraicGeometry.Scheme.pullbackG g n x) := by
  rw [AlgebraicGeometry.Scheme.pullbackG_comp]
  rfl

/-- The new flat G-map agrees with the already-existing open restriction. -/
theorem originalOpenRestriction {X Y : AlgebraicGeometry.Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (j : X ⟶ Y)
    [IsOpenImmersion j] (n : ℕ) :
    AlgebraicGeometry.Scheme.pullbackG j n = AlgebraicGeometry.Scheme.restrictG j n :=
  AlgebraicGeometry.Scheme.pullbackG_eq_restrictG j n

/-- The natural square uses the original public K, G and K-to-G maps. -/
theorem originalComparisonSquare {X Y : AlgebraicGeometry.Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y) [Flat f]
    (n : ℕ) (x : AlgebraicGeometry.Scheme.K Y n) :
    AlgebraicGeometry.Scheme.pullbackG f n (AlgebraicGeometry.Scheme.KToG Y n x) =
      AlgebraicGeometry.Scheme.KToG X n (AlgebraicGeometry.Scheme.pullbackK f n x) :=
  AlgebraicGeometry.Scheme.KToG_pullback_apply f n x

end QuillenTest.CoherentFlatPullback
