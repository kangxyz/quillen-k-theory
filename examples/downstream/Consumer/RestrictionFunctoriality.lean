import Quillen.Scheme.OpenImmersionFunctor
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Consumer.RestrictionFunctoriality

-- These tests use only the public group and restriction-map names.
example (X : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
    Quillen.Scheme.restrictK (𝟙 X) n = MonoidHom.id (Quillen.Scheme.K X n) := by simp

example {V U X : AlgebraicGeometry.Scheme.{u}} (i : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion j] (n : ℕ) :
    Quillen.Scheme.restrictK (i ≫ j) n =
      (Quillen.Scheme.restrictK i n).comp (Quillen.Scheme.restrictK j n) := by simp

example (X : AlgebraicGeometry.Scheme.{u}) [IsLocallyNoetherian X] (n : ℕ) :
    Quillen.Scheme.restrictG (𝟙 X) n = MonoidHom.id (Quillen.Scheme.G X n) := by simp

example {V U X : AlgebraicGeometry.Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian U] [IsLocallyNoetherian V]
    (i : V ⟶ U) (j : U ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j] (n : ℕ) :
    Quillen.Scheme.restrictG (i ≫ j) n =
      (Quillen.Scheme.restrictG i n).comp (Quillen.Scheme.restrictG j n) := by simp

-- Three successive restrictions compose in the intended contravariant order.
theorem triple_K_restriction {W V U X : AlgebraicGeometry.Scheme.{u}}
    (h : W ⟶ V) (i : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion h] [IsOpenImmersion i] [IsOpenImmersion j]
    (n : ℕ) (x : Quillen.Scheme.K X n) :
    Quillen.Scheme.restrictK ((h ≫ i) ≫ j) n x =
      Quillen.Scheme.restrictK h n
        (Quillen.Scheme.restrictK i n (Quillen.Scheme.restrictK j n x)) := by simp

theorem triple_G_restriction {W V U X : AlgebraicGeometry.Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian U]
    [IsLocallyNoetherian V] [IsLocallyNoetherian W]
    (h : W ⟶ V) (i : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion h] [IsOpenImmersion i] [IsOpenImmersion j]
    (n : ℕ) (x : Quillen.Scheme.G X n) :
    Quillen.Scheme.restrictG ((h ≫ i) ≫ j) n x =
      Quillen.Scheme.restrictG h n
        (Quillen.Scheme.restrictG i n (Quillen.Scheme.restrictG j n x)) := by simp


-- Bundles only use categories whose morphisms are open immersions.
theorem bundled_K_map {X Y : Quillen.Scheme.OpenImmersionSchemes.{u}ᵒᵖ}
    (f : X ⟶ Y) (n : ℕ) :
    ((Quillen.Scheme.KOpenFunctor n).map f).hom =
      Quillen.Scheme.restrictK f.unop.hom n := rfl

theorem bundled_G_map {X Y : Quillen.Scheme.LocallyNoetherianOpenSchemes.{u}ᵒᵖ}
    (f : X ⟶ Y) (n : ℕ) :
    ((Quillen.Scheme.GOpenFunctor n).map f).hom =
      Quillen.Scheme.restrictG f.unop.hom.hom n := rfl

theorem bundled_comparison_natural
    {X Y : Quillen.Scheme.LocallyNoetherianOpenSchemes.{u}ᵒᵖ}
    (f : X ⟶ Y) (n : ℕ) :
    (Quillen.Scheme.KLocallyNoetherianOpenFunctor n).map f ≫
        (Quillen.Scheme.KToGOpenNatTrans n).app Y =
      (Quillen.Scheme.KToGOpenNatTrans n).app X ≫
        (Quillen.Scheme.GOpenFunctor n).map f :=
  (Quillen.Scheme.KToGOpenNatTrans n).naturality f

end Consumer.RestrictionFunctoriality
