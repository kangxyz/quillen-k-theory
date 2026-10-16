/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.ExactCategory.Functor
public import Aglib.CategoryTheory.ExactCategory.BaseChange
public import Quillen.Aglib.CategoryTheory.ExactCategory.Inflations

/-! # Specified cokernels under exact functors

The original admissible-inflation cokernel belongs to its conflation
and remains a cokernel under an exact additive functor. The compatibility
lemma delegates to the canonical Aglib conflation criterion. The original
exact functor also maps the wide category of admissible monomorphisms.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v'
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

/-- Any actual cokernel of an admissible inflation belongs to its conflation. -/
lemma conflation_of_isCokernel (E : ExactStructure C) {X Y Z : C}
    {i : X ⟶ Y} {p : Y ⟶ Z} (h : i ≫ p = 0)
    (hp : IsColimit (CokernelCofork.ofπ p h)) (hi : E.inflation i) :
    E.conflation (ShortComplex.mk i p h) :=
  E.conflation_of_inflation_of_isCokernel hi hp

end CategoryTheory.ExactCategory.ExactStructure

namespace CategoryTheory.ExactCategory.ExactFunctor
variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  {E : ExactStructure C} {E' : ExactStructure D} (F : ExactFunctor E E')

/-- Exactness preserves the specified cokernel of an admissible inflation. -/
def mapInflationCokernel {X Y Z : C} {i : X ⟶ Y} {p : Y ⟶ Z}
    (h : i ≫ p = 0) (hp : IsColimit (CokernelCofork.ofπ p h)) (hi : E.inflation i) :
    IsColimit (CokernelCofork.ofπ (F.toFunctor.map p)
      (show F.toFunctor.map i ≫ F.toFunctor.map p = 0 by
        rw [← F.toFunctor.map_comp, h, F.toFunctor.map_zero])) :=
  E'.cokernel _ (F.map_conflation _ (E.conflation_of_isCokernel h hp hi))

/-- An exact functor sends the actual admissible-inflation category to its target. -/
def inflationFunctor : E.InflationCategory ⥤ E'.InflationCategory where
  obj X := ⟨F.toFunctor.obj X.obj⟩
  map f := ⟨F.toFunctor.map f.hom, F.map_inflation f.hom f.property⟩
  map_id X := WideSubcategory.hom_ext E'.inflation (F.toFunctor.map_id X.obj)
  map_comp f g := WideSubcategory.hom_ext E'.inflation (F.toFunctor.map_comp f.hom g.hom)

end CategoryTheory.ExactCategory.ExactFunctor
