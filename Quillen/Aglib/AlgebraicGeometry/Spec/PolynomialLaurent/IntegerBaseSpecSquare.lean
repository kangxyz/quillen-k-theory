/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.IndexSquare
public import Aglib.AlgebraicGeometry.BaseChange.Coefficients.PolynomialLaurent

/-! # The actual integral affine index square and original Laurent unit

The intended upstream module is
`Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.IntegerBaseSpecSquare`.
The construction uses arbitrary objects and morphisms under
`CommRingCat.of (ULift.{u} ℤ)` and the original affine polynomial/Laurent square;
the unit comparison applies to every `CommRingCat.{u}`. The current production
consumer is `Quillen.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.IntegerBaseParameterRow`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open CommRingCat.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec

/-- The actual spectrum of the underlying integral coefficient algebra. -/
def specUnder : Under (CommRingCat.of (ULift.{u} ℤ)) ⥤ Scheme.{u}ᵒᵖ where
  obj a := op (Spec a.right)
  map f := (Spec.map f.right).op
  map_id a := by exact congrArg Quiver.Hom.op (Spec.map_id a.right)
  map_comp f g := by exact congrArg Quiver.Hom.op (Spec.map_comp f.right g.right)

/-- All four original affine corners and both charts, in the index-change direction. -/
def specSquareIso (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    square (specUnder.obj a) ≅
      specUnder.mapArrow.mapArrow.obj (laurentUnderSquare _ a) :=
  Arrow.isoMk
    (Arrow.isoMk (Iso.refl _) (polynomialSpecIso a.right).op (by
      apply Quiver.Hom.unop_inj
      change polynomialProjection a.right =
        (polynomialSpecIso a.right).hom ≫ pullback.fst _ _
      exact (polynomialSpecIso_hom_fst a.right).symm))
    (Arrow.isoMk (polynomialSpecIso a.right).op (laurentSpecIso a.right).op (by
      apply Quiver.Hom.unop_inj
      exact polynomialLaurentSpecIso_minus a.right)) (by
        apply Arrow.hom_ext
        · apply Quiver.Hom.unop_inj
          change polynomialProjection a.right =
            (polynomialSpecIso a.right).hom ≫ pullback.fst _ _
          exact (polynomialSpecIso_hom_fst a.right).symm
        · apply Quiver.Hom.unop_inj
          exact polynomialLaurentSpecIso_plus a.right)

/-- The complete affine index square is natural for every original coefficient morphism. -/
theorem specSquareIso_naturality
    {a b : Under (CommRingCat.of (ULift.{u} ℤ))} (f : a ⟶ b) :
    squareFunctor.map (specUnder.map f) ≫ (specSquareIso b).hom =
      (specSquareIso a).hom ≫
        specUnder.mapArrow.mapArrow.map ((laurentUnderSquareFunctor _).map f) := by
  apply Arrow.hom_ext <;> apply Arrow.hom_ext
  · simp only [specSquareIso, squareFunctor, squareMap, specUnder]
    rfl
  · exact Quiver.Hom.unop_inj (polynomialSpecIso_naturality f.right).symm
  · exact Quiver.Hom.unop_inj (polynomialSpecIso_naturality f.right).symm
  · exact Quiver.Hom.unop_inj (laurentSpecIso_naturality f.right).symm

/-- The actual finite-square comparison, before applying any spectrum or tower functor. -/
def specSquare : specUnder.{u} ⋙ squareFunctor ≅
    laurentUnderSquareFunctor (CommRingCat.of (ULift.{u} ℤ)) ⋙
      specUnder.mapArrow.mapArrow :=
  NatIso.ofComponents specSquareIso (fun f => specSquareIso_naturality f)

/-- The original affine Laurent unit pulls back from the actual integer product unit. -/
theorem nativeLaurentUnit_spec (A : CommRingCat.{u}) :
    Units.map (laurentSpecIso A).hom.appTop.hom.toMonoidHom
      (Units.map (pullback.snd (toIntegerBase (Spec A))
        (laurentProjection integerRing)).appTop.hom.toMonoidHom
          (laurentGlobalUnit integerRing)) = laurentGlobalUnit A := by
  rw [← laurentGlobalUnit_coefficient (integerMap A)]
  apply Units.ext
  have h := congrArg (fun g => g.appTop) (laurentSpecIso_hom_snd A)
  rw [Scheme.Hom.comp_appTop] at h
  exact ConcreteCategory.congr_hom h (↑(laurentGlobalUnit integerRing))

end AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
