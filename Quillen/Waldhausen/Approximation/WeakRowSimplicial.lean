/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.Approximation.WeakRows
public import Quillen.Waldhausen.QuillenComparison.RowSimplicial

/-! # The simplicial categories of genuine weak-equivalence quotient rows -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe v u

namespace Quillen.Waldhausen

open QuillenComparison

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : CategoryTheory.ExactCategory.ExactStructure C) (cof weq : MorphismProperty C)
    [weq.IsMultiplicative]

/-- Reindexing retains the actual horizontal cofibrations and weak maps. -/
def weakRowReindex {m n : SimplexCategory} (α : m ⟶ n) :
    WeakRow E cof weq n ⥤ WeakRow E cof weq m where
  obj F := {
    row := (rowReindex E α).obj F.row
    cofibration i j k hij hjk := F.cofibration _ _ _
      (α.toOrderHom.monotone hij) (α.toOrderHom.monotone hjk) }
  map η := ⟨Functor.whiskerLeft (intervalMap α) η.val, fun p ↦ η.property _⟩

/-- The actual simplicial category with pointwise weak-equivalence maps. -/
def weakRowSimplicial : SimplexCategoryᵒᵖ ⥤ Cat.{v, max u v} where
  obj n := Cat.of (WeakRow E cof weq n.unop)
  map α := Cat.Hom.ofFunctor (weakRowReindex E cof weq α.unop)
  map_id _ := by
    apply Cat.Hom.ext
    apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
  map_comp _ _ := by
    apply Cat.Hom.ext
    apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The bisimplicial nerve before taking the genuine S-diagonal. -/
def weakRowNerve : SimplexCategoryᵒᵖ ⥤ SSet.{max u v} :=
  weakRowSimplicial E cof weq ⋙ nerveFunctor

variable (cof' : MorphismProperty C) (h : cof ≤ cof')

/-- The canonical inclusion is strictly simplicially natural. -/
def weakRowSimplicialInclusion :
    weakRowSimplicial E cof weq ⟶ weakRowSimplicial E cof' weq where
  app _ := Cat.Hom.ofFunctor (WeakRow.inclusion cof' h)
  naturality _ _ _ := by
    apply Cat.Hom.ext
    apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The actual bisimplicial nerve map for a change of cofibrations. -/
def weakRowNerveInclusion : weakRowNerve E cof weq ⟶ weakRowNerve E cof' weq :=
  Functor.whiskerRight (weakRowSimplicialInclusion E cof weq cof' h) nerveFunctor

end Quillen.Waldhausen
