/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.QuillenComparison.RowGroupoid
public import Quillen.Waldhausen.QuillenComparison.EdgewiseIndices
public import Quillen.CategoryTheory.TheoremA.Diagonal

/-! # The simplicial groupoid of exact S-rows -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe v u

namespace Quillen.Waldhausen.QuillenComparison

/-- Simultaneous reindexing of both endpoints in the arrow poset. -/
def intervalMap {m n : SimplexCategory} (α : m ⟶ n) : Interval m ⥤ Interval n :=
  (show Monotone (fun p : Interval m ↦
    interval (α.toOrderHom p.1.1) (α.toOrderHom p.1.2) (α.toOrderHom.monotone p.2)) from
    fun _ _ h ↦ ⟨α.toOrderHom.monotone h.1, α.toOrderHom.monotone h.2⟩).functor

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : CategoryTheory.ExactCategory.ExactStructure C)

/-- Restriction is a functor on the groupoid of exact S-rows. -/
def rowReindex {m n : SimplexCategory} (α : m ⟶ n) : Row E n ⥤ Row E m where
  obj F := ⟨intervalMap α ⋙ F.diagram,
    F.simplex.precomp E.inflation (MorphismProperty.isomorphisms C) α⟩
  map e := Functor.isoWhiskerLeft (intervalMap α) e
  map_id _ := by apply Iso.ext; rfl
  map_comp _ _ := by apply Iso.ext; rfl

/-- The actual S-construction, before taking the diagonal nerve. -/
def rowSimplicial : SimplexCategoryᵒᵖ ⥤ Cat.{v, max u v} where
  obj n := Cat.of (Row E n.unop)
  map α := Cat.Hom.ofFunctor (rowReindex E α.unop)
  map_id _ := by
    apply Cat.Hom.ext
    apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
  map_comp _ _ := by
    apply Cat.Hom.ext
    apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The bisimplicial nerve of the actual S-row groupoids. -/
def rowNerve : SimplexCategoryᵒᵖ ⥤ SSet.{max u v} := rowSimplicial E ⋙ nerveFunctor

/-- The central nested intervals, without the original nerve coordinate. -/
def centralIntervalFunctor (n : SimplexCategory) :
    Fin (n.len + 1) ⥤ NestedInterval (Edgewise.ε.obj n) where
  obj := centralInterval n
  map f := homOfLE ⟨lowerIndex_antitone n (leOfHom f), upperIndex_monotone n (leOfHom f)⟩
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The comparison on exact rows takes values in the full isomorphism
groupoid of composable Q-arrows. -/
def rowChainComparison (n : SimplexCategory) :
    Row E (Edgewise.ε.obj n) ⥤ Core (ComposableArrows (Q E.deflation E.inflation) n.len) where
  obj F := ⟨centralIntervalFunctor n ⋙ rowIntervalFunctor E F⟩
  map e := ⟨Functor.isoWhiskerLeft (centralIntervalFunctor n) (rowIntervalIso E e)⟩
  map_id F := by
    apply Core.hom_ext
    ext p
    rfl
  map_comp e f := by
    apply Core.hom_ext
    ext p
    change (E.qIsoOfIso ((e ≫ f).app _)).hom =
      (E.qIsoOfIso (e.app _)).hom ≫ (E.qIsoOfIso (f.app _)).hom
    change (E.qIsoOfIso (e.app _ ≪≫ f.app _)).hom = _
    rw [CategoryTheory.ExactCategory.ExactStructure.qIsoOfIso_trans, Iso.trans_hom]

end Quillen.Waldhausen.QuillenComparison
