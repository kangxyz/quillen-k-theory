/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Waldhausen.QuillenComparison.Reindexing
public import Mathlib.CategoryTheory.Core

/-! # The groupoid of exact quotient rows

Objects are actual exact S-rows, and morphisms are natural isomorphisms of
their quotient diagrams. The subquotient-span construction is functorial on
this groupoid, retaining every quotient and every component isomorphism.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe v u

namespace Quillen.Waldhausen.QuillenComparison

/-- Forget the nerve coordinate of a grid. -/
def gridProjection (n : SimplexCategory) : Grid n ⥤ Interval n :=
  (show Monotone (fun p : Grid n ↦ p.2) from fun _ _ h ↦ h.2).functor

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : Quillen.ExactStructure C)

/-- A quotient row satisfying the actual exact S-construction conditions.
The constant nerve direction only records identity isomorphisms. -/
@[ext]
structure Row (n : SimplexCategory) where
  /-- The diagram of actual subquotient objects indexed by `Interval n`; pulling it back along
  `gridProjection n` gives the exact S-simplex. -/
  diagram : Interval n ⥤ C
  simplex : IsSimplex E.inflation (MorphismProperty.isomorphisms C)
    (gridProjection n ⋙ diagram)

namespace Row

variable {E} {n : SimplexCategory}

/-- Morphisms of exact quotient rows are their actual natural isomorphisms. -/
instance : Groupoid (Row E n) where
  Hom F G := F.diagram ≅ G.diagram
  id F := Iso.refl F.diagram
  comp f g := f ≪≫ g
  id_comp f := by apply Iso.ext; simp
  comp_id f := by apply Iso.ext; simp
  assoc f g h := by apply Iso.ext; simp
  inv f := f.symm
  inv_comp f := by apply Iso.ext; simp
  comp_inv f := by apply Iso.ext; simp

end Row

variable {n : SimplexCategory}

/-- The canonical Q-valued interval functor associated to an exact row. -/
def rowIntervalFunctor (F : Row E n) : NestedInterval n ⥤ Q E.deflation E.inflation :=
  intervalQFunctor E F.simplex 0

/-- A natural isomorphism of exact rows induces a natural isomorphism of
their actual Q-valued interval functors. -/
def rowIntervalIso {F G : Row E n} (e : F ⟶ G) :
    rowIntervalFunctor E F ≅ rowIntervalFunctor E G :=
  NatIso.ofComponents
    (fun p ↦ E.qIsoOfIso (e.app (interval p.left p.right p.endpoints))) (by
      intro p q f
      apply qSpan_iso_naturality E
        (intervalSpan E F.simplex 0 (leOfHom f)) (intervalSpan E G.simplex 0 (leOfHom f))
        (e.app (interval p.left p.right p.endpoints))
        (e.app (interval q.left q.right q.endpoints))
        (e.app (interval q.left p.right ((NestedInterval.left_anti (leOfHom f)).trans p.endpoints)))
      · exact e.hom.naturality _
      · exact e.hom.naturality _)

/-- This comparison is a functor on the full groupoid of exact quotient rows. -/
def rowIntervalComparison : Row E n ⥤ (NestedInterval n ⥤ Q E.deflation E.inflation) where
  obj := rowIntervalFunctor E
  map e := (rowIntervalIso E e).hom
  map_id F := by
    ext p
    rfl
  map_comp e f := by
    ext p
    change (E.qIsoOfIso ((e ≫ f).app _)).hom =
      (E.qIsoOfIso (e.app _)).hom ≫ (E.qIsoOfIso (f.app _)).hom
    change (E.qIsoOfIso (e.app _ ≪≫ f.app _)).hom = _
    rw [ExactStructure.qIsoOfIso_trans, Iso.trans_hom]

end Quillen.Waldhausen.QuillenComparison
