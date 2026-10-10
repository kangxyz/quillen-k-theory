/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Waldhausen.QuillenComparison.VerticalSpans
public import Mathlib.CategoryTheory.Functor.Currying

/-! # Reindexing the subquotient comparison

The actual Q-valued bifunctor of an exact S-simplex commutes strictly with
simultaneous reindexing of the nerve and interval directions.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial CategoryTheory.Prod
universe v u

namespace Quillen.Waldhausen.QuillenComparison

/-- An increasing ordinal map preserves containment of intervals. -/
def nestedIntervalMap {m n : SimplexCategory} (α : m ⟶ n) :
    NestedInterval m ⥤ NestedInterval n where
  obj p := ⟨(OrderDual.toDual (α.toOrderHom p.left), α.toOrderHom p.right),
    α.toOrderHom.monotone p.endpoints⟩
  map f := homOfLE ⟨α.toOrderHom.monotone (NestedInterval.left_anti (leOfHom f)),
    α.toOrderHom.monotone (NestedInterval.right_mono (leOfHom f))⟩
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : Quillen.ExactStructure C)
variable {n : SimplexCategory} {F : Grid n ⥤ C}
variable (hF : IsSimplex E.inflation (MorphismProperty.isomorphisms C) F)

/-- The comparison on both directions, before selecting the central diagonal. -/
def gridQFunctor : Fin (n.len + 1) × NestedInterval n ⥤ Q E.deflation E.inflation :=
  Functor.uncurry.obj (rowsQFunctor E hF)

/-- Every ordinal reindexing agrees with reindexing the Q-valued bifunctor. -/
theorem gridQFunctor_precomp {m : SimplexCategory} (α : m ⟶ n) :
    gridQFunctor E (hF.precomp E.inflation (MorphismProperty.isomorphisms C) α) =
      ((SimplexCategory.toCat.map α).toFunctor.prod (nestedIntervalMap α)) ⋙
        gridQFunctor E hF := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

end Quillen.Waldhausen.QuillenComparison
