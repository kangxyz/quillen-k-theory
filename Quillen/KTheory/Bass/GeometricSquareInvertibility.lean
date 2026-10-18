/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.GeometricSquareInterchange

/-!
# Invertibility of the actual geometric Bass square interchange

The actual square map is invertible because its source component is identity
and its remaining three components are the original factor-interchange
isomorphisms. The proof uses the component criterion in the arrow category
twice and introduces no additional compatibility hypothesis.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.LoopPrespectrum
universe u w u₁ v₁
namespace Quillen.KTheory.Bass.GeometricSquareInterchange
variable (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})

/-- The lower polynomial corner is the same original factor interchange. -/
theorem squareInterchange_polynomial_lower : (squareInterchangeMap F).right.left =
    (eta (polynomialProjection (.of (ULift.{u} ℤ))) F).hom :=
  Arrow.squareMapHomMk_right_left _ _ _ _ _ _ _ _ _ _ _

private theorem isIso_of_eq {C : Type u₁} [Category.{v₁} C]
    {X Y : C} {f g : X ⟶ Y} (h : f = g) (hg : IsIso g) : IsIso f :=
  h.symm ▸ hg

/-- The original geometric square interchange is an isomorphism. -/
theorem squareInterchange_isIso : IsIso (squareInterchangeMap F) := by
  have : IsIso (squareInterchangeMap F).left.left :=
    isIso_of_eq (squareInterchange_base F)
      (IsIso.id ((strictDiagramFunctor squareFunctor).obj F))
  have : IsIso (squareInterchangeMap F).left.right :=
    isIso_of_eq (squareInterchange_polynomial F)
      (eta (polynomialProjection (.of (ULift.{u} ℤ))) F).isIso_hom
  have : IsIso (squareInterchangeMap F).right.left :=
    isIso_of_eq (squareInterchange_polynomial_lower F)
      (eta (polynomialProjection (.of (ULift.{u} ℤ))) F).isIso_hom
  have : IsIso (squareInterchangeMap F).right.right :=
    isIso_of_eq (squareInterchange_laurent F)
      (eta (laurentProjection (.of (ULift.{u} ℤ))) F).isIso_hom
  have : IsIso (squareInterchangeMap F).left :=
    Arrow.isIso_of_isIso_left_of_isIso_right _
  have : IsIso (squareInterchangeMap F).right :=
    Arrow.isIso_of_isIso_left_of_isIso_right _
  exact Arrow.isIso_of_isIso_left_of_isIso_right _

end Quillen.KTheory.Bass.GeometricSquareInterchange
