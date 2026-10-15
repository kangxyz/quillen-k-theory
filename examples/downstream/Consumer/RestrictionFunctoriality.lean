/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.OpenImmersionFunctor

/-!
# Scheme K-theory and G-theory restriction examples

Records identity, composition, and triple restriction in contravariant order
using the public group and restriction names. The bundled-functor statements
identify the same maps and express naturality of the K-to-G comparison.
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Consumer.RestrictionFunctoriality

-- These tests use only the public group and restriction-map names.
example (X : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
    AlgebraicGeometry.Scheme.restrictK (𝟙 X) n = MonoidHom.id (AlgebraicGeometry.Scheme.K X n) := by
      simp

example {V U X : AlgebraicGeometry.Scheme.{u}} (i : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion j] (n : ℕ) :
    AlgebraicGeometry.Scheme.restrictK (i ≫ j) n =
      (AlgebraicGeometry.Scheme.restrictK i n).comp (AlgebraicGeometry.Scheme.restrictK j n) := by
        simp

example (X : AlgebraicGeometry.Scheme.{u}) [IsLocallyNoetherian X] (n : ℕ) :
    AlgebraicGeometry.Scheme.restrictG (𝟙 X) n = MonoidHom.id (AlgebraicGeometry.Scheme.G X n) := by
      simp

example {V U X : AlgebraicGeometry.Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian U] [IsLocallyNoetherian V]
    (i : V ⟶ U) (j : U ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j] (n : ℕ) :
    AlgebraicGeometry.Scheme.restrictG (i ≫ j) n =
      (AlgebraicGeometry.Scheme.restrictG i n).comp (AlgebraicGeometry.Scheme.restrictG j n) := by
        simp

-- Three successive restrictions compose in the intended contravariant order.
theorem triple_K_restriction {W V U X : AlgebraicGeometry.Scheme.{u}}
    (h : W ⟶ V) (i : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion h] [IsOpenImmersion i] [IsOpenImmersion j]
    (n : ℕ) (x : AlgebraicGeometry.Scheme.K X n) :
    AlgebraicGeometry.Scheme.restrictK ((h ≫ i) ≫ j) n x =
      AlgebraicGeometry.Scheme.restrictK h n
        (AlgebraicGeometry.Scheme.restrictK i n (AlgebraicGeometry.Scheme.restrictK j n x)) := by
          simp

theorem triple_G_restriction {W V U X : AlgebraicGeometry.Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian U]
    [IsLocallyNoetherian V] [IsLocallyNoetherian W]
    (h : W ⟶ V) (i : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion h] [IsOpenImmersion i] [IsOpenImmersion j]
    (n : ℕ) (x : AlgebraicGeometry.Scheme.G X n) :
    AlgebraicGeometry.Scheme.restrictG ((h ≫ i) ≫ j) n x =
      AlgebraicGeometry.Scheme.restrictG h n
        (AlgebraicGeometry.Scheme.restrictG i n (AlgebraicGeometry.Scheme.restrictG j n x)) := by
          simp


-- Bundles only use categories whose morphisms are open immersions.
theorem bundled_K_map {X Y : AlgebraicGeometry.Scheme.OpenImmersionSchemes.{u}ᵒᵖ}
    (f : X ⟶ Y) (n : ℕ) :
    ((AlgebraicGeometry.Scheme.KOpenFunctor n).map f).hom =
      AlgebraicGeometry.Scheme.restrictK f.unop.hom n := rfl

theorem bundled_G_map {X Y : AlgebraicGeometry.Scheme.LocallyNoetherianOpenSchemes.{u}ᵒᵖ}
    (f : X ⟶ Y) (n : ℕ) :
    ((AlgebraicGeometry.Scheme.GOpenFunctor n).map f).hom =
      AlgebraicGeometry.Scheme.restrictG f.unop.hom.hom n := rfl

theorem bundled_comparison_natural
    {X Y : AlgebraicGeometry.Scheme.LocallyNoetherianOpenSchemes.{u}ᵒᵖ}
    (f : X ⟶ Y) (n : ℕ) :
    (AlgebraicGeometry.Scheme.KLocallyNoetherianOpenFunctor n).map f ≫
        (AlgebraicGeometry.Scheme.KToGOpenNatTrans n).app Y =
      (AlgebraicGeometry.Scheme.KToGOpenNatTrans n).app X ≫
        (AlgebraicGeometry.Scheme.GOpenFunctor n).map f :=
  (AlgebraicGeometry.Scheme.KToGOpenNatTrans n).naturality f

end Consumer.RestrictionFunctoriality
