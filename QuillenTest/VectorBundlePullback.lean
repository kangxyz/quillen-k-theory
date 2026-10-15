/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Pullback
public import Quillen.AlgebraicGeometry.Scheme.OpenImmersionFunctor

/-!
# Consumers for arbitrary vector-bundle pullback

These examples use arbitrary scheme and affine morphisms, exactness for an
ambient sequence with finite locally free quotient, and agreement with the
existing open-restriction functor.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace QuillenTest.VectorBundlePullback

open Quillen

/-- An arbitrary map of affine schemes has a contravariant bundle K-map,
without flatness or open-immersion assumptions. -/
def affinePullback {R S : CommRingCat.{u}} (φ : R ⟶ S) (n : ℕ) :
    AlgebraicGeometry.Scheme.K (Spec R) n →* AlgebraicGeometry.Scheme.K (Spec S) n :=
  AlgebraicGeometry.Scheme.pullbackK (Spec.map φ) n

/-- Pulling back a finite free sheaf along an arbitrary morphism retains the
same finite generator type. -/
def finiteFreePullback {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (Scheme.Modules.pullback f).obj (AlgebraicGeometry.Scheme.Modules.finiteFree (X := Y) n).obj ≅
      (AlgebraicGeometry.Scheme.Modules.finiteFree (X := X) n).obj :=
  AlgebraicGeometry.Scheme.Modules.pullbackFreeIso f (ULift (Fin n))

/-- Even when the first two sheaves are not assumed finite locally free,
a finite locally free quotient suffices for pullback exactness. -/
theorem exactWithBundleQuotient {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    (S : ShortComplex Y.Modules) (hS : S.ShortExact)
    [AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree Y S.X₃] :
    (S.map (Scheme.Modules.pullback f)).ShortExact :=
  AlgebraicGeometry.Scheme.Modules.shortExact_pullback f hS

/-- The full-scheme K-functor retains the original open-restriction map. -/
theorem existingOpenMap {X Y : AlgebraicGeometry.Scheme.OpenImmersionSchemes.{u}ᵒᵖ}
    (f : X ⟶ Y) (n : ℕ) :
    ((AlgebraicGeometry.Scheme.KOpenFunctor n).map f).hom =
      AlgebraicGeometry.Scheme.pullbackK f.unop.hom n :=
  (AlgebraicGeometry.Scheme.pullbackK_eq_restrictK f.unop.hom n).symm

/-- Successive arbitrary pullbacks compute the map of the composite. -/
theorem composablePullbacks {X Y Z : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) (x : AlgebraicGeometry.Scheme.K Z n) :
    AlgebraicGeometry.Scheme.pullbackK (f ≫ g) n x =
      AlgebraicGeometry.Scheme.pullbackK f n (AlgebraicGeometry.Scheme.pullbackK g n x) := by
  rw [AlgebraicGeometry.Scheme.pullbackK_comp]
  rfl

end QuillenTest.VectorBundlePullback
