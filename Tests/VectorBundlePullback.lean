/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Scheme.Pullback
import Quillen.Scheme.OpenImmersionFunctor

/-!
# Consumers for arbitrary vector-bundle pullback

These examples use arbitrary scheme and affine morphisms, exactness for an
ambient sequence with finite locally free quotient, and agreement with the
existing open-restriction functor.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Quillen.Tests.VectorBundlePullback

/-- An arbitrary map of affine schemes has a contravariant bundle K-map,
without flatness or open-immersion assumptions. -/
def affinePullback {R S : CommRingCat.{u}} (φ : R ⟶ S) (n : ℕ) :
    Quillen.Scheme.K (Spec R) n →* Quillen.Scheme.K (Spec S) n :=
  Quillen.Scheme.pullbackK (Spec.map φ) n

/-- Pulling back a finite free sheaf along an arbitrary morphism retains the
same finite generator type. -/
def finiteFreePullback {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (Scheme.Modules.pullback f).obj (SchemeSheaf.finiteFree (X := Y) n).obj ≅
      (SchemeSheaf.finiteFree (X := X) n).obj :=
  SchemeSheaf.pullbackFreeIso f (ULift (Fin n))

/-- Even when the first two sheaves are not assumed finite locally free,
a finite locally free quotient suffices for pullback exactness. -/
theorem exactWithBundleQuotient {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    (S : ShortComplex Y.Modules) (hS : S.ShortExact)
    [SchemeSheaf.IsFiniteLocallyFree Y S.X₃] :
    (S.map (Scheme.Modules.pullback f)).ShortExact :=
  SchemeSheaf.shortExact_pullback f hS

/-- The full-scheme K-functor retains the original open-restriction map. -/
theorem existingOpenMap {X Y : Quillen.Scheme.OpenImmersionSchemes.{u}ᵒᵖ}
    (f : X ⟶ Y) (n : ℕ) :
    ((Quillen.Scheme.KOpenFunctor n).map f).hom =
      Quillen.Scheme.pullbackK f.unop.hom n :=
  (Quillen.Scheme.pullbackK_eq_restrictK f.unop.hom n).symm

/-- Successive arbitrary pullbacks compute the map of the composite. -/
theorem composablePullbacks {X Y Z : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) (x : Quillen.Scheme.K Z n) :
    Quillen.Scheme.pullbackK (f ≫ g) n x =
      Quillen.Scheme.pullbackK f n (Quillen.Scheme.pullbackK g n x) := by
  rw [Quillen.Scheme.pullbackK_comp]
  rfl

end Quillen.Tests.VectorBundlePullback
