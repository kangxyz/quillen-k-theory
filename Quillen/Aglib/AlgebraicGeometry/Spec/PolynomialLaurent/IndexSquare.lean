/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Aglib.AlgebraicGeometry.Products.IntegerBaseInterchange
public import Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.Basic
public import Mathlib.CategoryTheory.Comma.Arrow

/-!
# The original Bass index square on arbitrary schemes

The positive and inverse charts define a genuine square functor on all schemes,
with no quasi-compactness hypotheses. Independent integer-base products commute
with this square by the original four swaps. The first component is identity;
the other components have the contravariant direction required by geometric K-theory.

Intended general owner: Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.IndexSquare.
The immediate consumer is the finite Bass seed interchange, not a tower construction.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

namespace AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex

/-- The original polynomial product, now on every scheme. -/
def polynomial : Scheme.{u} ⥤ Scheme.{u} :=
  baseProductFunctor (polynomialProjection (.of (ULift.{u} ℤ)))

/-- The original Laurent product on every scheme. -/
def laurent : Scheme.{u} ⥤ Scheme.{u} :=
  baseProductFunctor (laurentProjection (.of (ULift.{u} ℤ)))

/-- The actual positive coordinate chart. -/
def plus : laurent.{u} ⟶ polynomial.{u} :=
  baseProductTransformation _ _ (laurentPlus (.of (ULift.{u} ℤ)))
    (laurentPlus_projection (.of (ULift.{u} ℤ)))

/-- The actual inverse coordinate chart. -/
def minus : laurent.{u} ⟶ polynomial.{u} :=
  baseProductTransformation _ _ (laurentMinus (.of (ULift.{u} ℤ)))
    (laurentMinus_projection (.of (ULift.{u} ℤ)))

/-- The original projection from the polynomial product. -/
def projection : polynomial.{u} ⟶ 𝟭 _ := baseProductProjection _

/-- Both charts have exactly the same original projection to the base. -/
theorem chart_projection (X : Scheme.{u}) :
    plus.app X ≫ projection.app X = minus.app X ≫ projection.app X := by
  change (baseProductTransformation _ _ _ _).app X ≫ (baseProductProjection _).app X =
    (baseProductTransformation _ _ _ _).app X ≫ (baseProductProjection _).app X
  rw [baseProductTransformation_projection, baseProductTransformation_projection]

/-- The original four-corner square in the opposite scheme category. -/
def square (X : Scheme.{u}ᵒᵖ) : Arrow (Arrow Scheme.{u}ᵒᵖ) :=
  Arrow.mk (Arrow.homMk (f := Arrow.mk (projection.app X.unop).op)
    (g := Arrow.mk (minus.app X.unop).op)
    (projection.app X.unop).op (plus.app X.unop).op
    (Quiver.Hom.unop_inj (chart_projection X.unop).symm))

/-- Every original scheme morphism acts on all four corners. -/
def squareMap {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y) : square X ⟶ square Y :=
  Arrow.homMk
    (Arrow.homMk f (polynomial.map f.unop).op
      (Quiver.Hom.unop_inj (projection.naturality f.unop).symm))
    (Arrow.homMk (polynomial.map f.unop).op (laurent.map f.unop).op
      (Quiver.Hom.unop_inj (minus.naturality f.unop).symm)) (by
        apply Arrow.hom_ext
        · exact Quiver.Hom.unop_inj (projection.naturality f.unop).symm
        · exact Quiver.Hom.unop_inj (plus.naturality f.unop).symm)

/-- The original Bass evaluation square is strictly natural on arbitrary schemes. -/
def squareFunctor : Scheme.{u}ᵒᵖ ⥤ Arrow (Arrow Scheme.{u}ᵒᵖ) where
  obj := square
  map := squareMap
  map_id X := by
    apply Arrow.hom_ext <;> apply Arrow.hom_ext
    · rfl
    · simp [squareMap, square]
    · simp [squareMap, square]
    · simp [squareMap, square]
  map_comp f g := by
    apply Arrow.hom_ext <;> apply Arrow.hom_ext
    · rfl
    · simp [squareMap, square]
    · simp [squareMap, square]
    · simp [squareMap, square]

variable {T : Scheme.{u}} (q : T ⟶ integerBase)

/-- The positive chart retains the whole original independent-variable swap square. -/
theorem swap_plus (X : Scheme.{u}) :
    (baseProductFunctor q).map (plus.app X) ≫
      (baseProductSwapIso (polynomialProjection (.of (ULift.{u} ℤ))) q).hom.app X =
    (baseProductSwapIso (laurentProjection (.of (ULift.{u} ℤ))) q).hom.app X ≫
      plus.app ((baseProductFunctor q).obj X) :=
  baseProductSwapIso_transformation_first _ _ q _ _ X

/-- The inverted chart retains the same literal independent-variable square. -/
theorem swap_minus (X : Scheme.{u}) :
    (baseProductFunctor q).map (minus.app X) ≫
      (baseProductSwapIso (polynomialProjection (.of (ULift.{u} ℤ))) q).hom.app X =
    (baseProductSwapIso (laurentProjection (.of (ULift.{u} ℤ))) q).hom.app X ≫
      minus.app ((baseProductFunctor q).obj X) :=
  baseProductSwapIso_transformation_first _ _ q _ _ X

/-- The actual four-corner index isomorphism, with the original positive and inverse charts. -/
def squareIso (X : Scheme.{u}ᵒᵖ) :
    square ((baseProductFunctor q).op.obj X) ≅
      (baseProductFunctor q).op.mapArrow.mapArrow.obj (square X) :=
  Arrow.isoMk
    (Arrow.isoMk (Iso.refl _) ((baseProductSwapIso
      (polynomialProjection (.of (ULift.{u} ℤ))) q).app X.unop).op (by
        apply Quiver.Hom.unop_inj
        simpa [square, projection] using (baseProductSwapIso_projection_first
          (polynomialProjection (.of (ULift.{u} ℤ))) q X.unop).symm))
    (Arrow.isoMk ((baseProductSwapIso
      (polynomialProjection (.of (ULift.{u} ℤ))) q).app X.unop).op
      ((baseProductSwapIso (laurentProjection (.of (ULift.{u} ℤ))) q).app X.unop).op
      (Quiver.Hom.unop_inj (swap_minus q X.unop))) (by
        apply Arrow.hom_ext
        · apply Quiver.Hom.unop_inj
          simpa [square, projection] using (baseProductSwapIso_projection_first
            (polynomialProjection (.of (ULift.{u} ℤ))) q X.unop).symm
        · exact Quiver.Hom.unop_inj (swap_plus q X.unop))

/-- The original base corner is fixed literally. -/
theorem squareIso_hom_base (X : Scheme.{u}ᵒᵖ) :
    (squareIso q X).hom.left.left = 𝟙 ((baseProductFunctor q).op.obj X) := rfl

/-- The polynomial component has precisely the original swap's contravariant direction. -/
theorem squareIso_hom_polynomial (X : Scheme.{u}ᵒᵖ) :
    (squareIso q X).hom.left.right =
      (baseProductSwapMap (polynomialProjection (.of (ULift.{u} ℤ))) q X.unop).op := rfl

/-- The Laurent corner retains the original, rather than an abstractly chosen, swap. -/
theorem squareIso_hom_laurent (X : Scheme.{u}ᵒᵖ) :
    (squareIso q X).hom.right.right =
      (baseProductSwapMap (laurentProjection (.of (ULift.{u} ℤ))) q X.unop).op := rfl

/-- The four-corner swap commutes with every original base-scheme morphism. -/
theorem squareIso_naturality {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y) :
    squareFunctor.map ((baseProductFunctor q).op.map f) ≫ (squareIso q Y).hom =
      (squareIso q X).hom ≫ (baseProductFunctor q).op.mapArrow.mapArrow.map
        (squareFunctor.map f) := by
  apply Arrow.hom_ext <;> apply Arrow.hom_ext
  · simp [squareIso, squareFunctor, squareMap]
  · exact Quiver.Hom.unop_inj (baseProductSwapMap_naturality _ q f.unop).symm
  · exact Quiver.Hom.unop_inj (baseProductSwapMap_naturality _ q f.unop).symm
  · exact Quiver.Hom.unop_inj (baseProductSwapMap_naturality _ q f.unop).symm

/-- Actual natural interchange between product-before-square and square-before-product. -/
def interchange : (baseProductFunctor q).op ⋙ squareFunctor ≅
    squareFunctor ⋙ (baseProductFunctor q).op.mapArrow.mapArrow :=
  NatIso.ofComponents (squareIso q) (squareIso_naturality q)

end AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
