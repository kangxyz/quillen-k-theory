/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.QuillenComparison.RowSimplicial

/-! # The genuine grid model is the diagonal row-groupoid nerve -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe v u

namespace Quillen.Waldhausen.QuillenComparison

/-- Include a quotient row at its specified nerve coordinate. -/
def rowRestriction {n : SimplexCategory} (t : Fin (n.len + 1)) : Interval n ⥤ Grid n :=
  (show Monotone (fun p : Interval n ↦ (t, p) : Interval n → Grid n) from
    fun _ _ h ↦ ⟨le_rfl, h⟩).functor

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : Quillen.ExactStructure C)
variable {n : SimplexCategory} {F : Grid n ⥤ C}
variable (hF : IsSimplex E.inflation (MorphismProperty.isomorphisms C) F)

/-- Extract an actual exact quotient row from the original diagonal simplex. -/
def gridRow (t : Fin (n.len + 1)) : Row E n where
  diagram := rowRestriction t ⋙ F
  simplex := {
    zero := fun _ i ↦ hF.zero t i
    cofibration := fun _ i j k hij hjk ↦ hF.cofibration t i j k hij hjk
    quotient := fun _ i j k hij hjk ↦ hF.quotient t i j k hij hjk
    weak := fun _ _ i j _ hij ↦ hF.weak t t i j le_rfl hij }

/-- The original vertical arrows give natural isomorphisms of extracted rows. -/
def gridRowIso (s t : Fin (n.len + 1)) (hst : s ≤ t) :
    gridRow E hF s ⟶ gridRow E hF t :=
  NatIso.ofComponents (fun p ↦ verticalIso E hF s t hst p.2) (by
    intro p q f
    exact rowMap_verticalMap s t hst p.2 q.2 (leOfHom f).1 (leOfHom f).2)

/-- Reorganize an original grid simplex as a chain in the exact-row groupoid. -/
def gridRows : ComposableArrows (Row E n) n.len where
  obj := gridRow E hF
  map f := gridRowIso E hF _ _ (leOfHom f)
  map_id t := by
    apply Iso.ext
    ext p
    exact F.map_id _
  map_comp f g := by
    apply Iso.ext
    ext p
    exact F.map_comp _ _

/-- Reassemble a chain of exact rows into the actual two-direction grid. -/
def rowsGrid (G : ComposableArrows (Row E n) n.len) : Grid n ⥤ C where
  obj p := (G.obj p.1).diagram.obj p.2
  map {p q} f := (G.map (homOfLE (leOfHom f).1)).hom.app p.2 ≫
    (G.obj q.1).diagram.map (homOfLE (leOfHom f).2)
  map_id p := by
    rcases p with ⟨t, p⟩
    change (G.map (𝟙 t)).hom.app p ≫ (G.obj t).diagram.map (𝟙 p) = _
    rw [G.map_id, (G.obj t).diagram.map_id]
    exact Category.id_comp _
  map_comp {p q r} f g := by
    rcases p with ⟨s, p⟩
    rcases q with ⟨t, q⟩
    rcases r with ⟨u, r⟩
    change (G.map ((homOfLE (leOfHom f).1) ≫ (homOfLE (leOfHom g).1))).hom.app p ≫
      (G.obj u).diagram.map ((homOfLE (leOfHom f).2) ≫ (homOfLE (leOfHom g).2)) = _
    rw [G.map_comp, (G.obj u).diagram.map_comp]
    change (_ ≫ _) ≫ (_ ≫ _) = (_ ≫ _) ≫ (_ ≫ _)
    simp only [Category.assoc]
    congr 1
    rw [← (G.map (homOfLE (leOfHom g).1)).hom.naturality_assoc]

/-- Reassembly retains zero diagonals, cofibrations, quotient pushouts and
actual vertical isomorphisms. -/
theorem rowsGrid_isSimplex (G : ComposableArrows (Row E n) n.len) :
    IsSimplex E.inflation (MorphismProperty.isomorphisms C) (rowsGrid E G) where
  zero t i := (G.obj t).simplex.zero 0 i
  cofibration t i j k hij hjk := by
    change E.inflation ((G.map (𝟙 t)).hom.app _ ≫ (G.obj t).diagram.map _)
    rw [G.map_id]
    change E.inflation (𝟙 _ ≫ (G.obj t).diagram.map _)
    rw [Category.id_comp]
    exact (G.obj t).simplex.cofibration 0 i j k hij hjk
  quotient t i j k hij hjk := by
    change IsPushout ((G.map (𝟙 t)).hom.app _ ≫ (G.obj t).diagram.map _)
      ((G.map (𝟙 t)).hom.app _ ≫ (G.obj t).diagram.map _)
      ((G.map (𝟙 t)).hom.app _ ≫ (G.obj t).diagram.map _)
      ((G.map (𝟙 t)).hom.app _ ≫ (G.obj t).diagram.map _)
    rw [G.map_id]
    change IsPushout (𝟙 _ ≫ (G.obj t).diagram.map _) (𝟙 _ ≫ (G.obj t).diagram.map _)
      (𝟙 _ ≫ (G.obj t).diagram.map _) (𝟙 _ ≫ (G.obj t).diagram.map _)
    simp only [Category.id_comp]
    exact (G.obj t).simplex.quotient 0 i j k hij hjk
  weak s t i j hst hij := by
    change IsIso ((G.map (homOfLE hst)).hom.app _ ≫
      (G.obj t).diagram.map (𝟙 _))
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
    infer_instance

/-- Extracting and reassembling the rows retains the original grid functor. -/
@[simp]
theorem rowsGrid_gridRows : rowsGrid E (gridRows E hF) = F := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro p q f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact (F.map_comp _ _).symm

@[simp]
theorem row_eqToHom_hom_app {F G : Row E n} (h : F = G) (p : Interval n) :
    (eqToHom h : F ⟶ G).hom.app p = eqToHom (congrArg (fun R : Row E n ↦ R.diagram.obj p) h) := by
  cases h
  rfl

/-- Reassembly and extraction retain the original chain of row isomorphisms. -/
@[simp]
theorem gridRows_rowsGrid (G : ComposableArrows (Row E n) n.len) :
    gridRows E (rowsGrid_isSimplex E G) = G := by
  have hobj (t : Fin (n.len + 1)) : gridRow E (rowsGrid_isSimplex E G) t = G.obj t := by
    apply Row.ext
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
    intro p q f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change (G.map (𝟙 t)).hom.app p ≫ (G.obj t).diagram.map f = _
    rw [G.map_id]
    exact Category.id_comp _
  refine CategoryTheory.Functor.ext hobj ?_
  intro s t f
  apply Iso.ext
  ext p
  change _ = (eqToHom (hobj s) : _ ⟶ _).hom.app p ≫ (G.map f).hom.app p ≫
    (eqToHom (hobj t).symm : _ ⟶ _).hom.app p
  simp only [row_eqToHom_hom_app, eqToHom_refl, Category.id_comp, Category.comp_id]
  change (G.map f).hom.app p ≫ (G.obj t).diagram.map (𝟙 p) = _
  rw [(G.obj t).diagram.map_id, Category.comp_id]

/-- The original S-grid simplicial set maps to the diagonal of the exact-row nerve. -/
def toRowDiagonal : sSet E.inflation (MorphismProperty.isomorphisms C) ⟶
    TheoremA.diagonalSSet (rowNerve E) where
  app _ := ↾fun F ↦ gridRows E F.2
  naturality n m α := by
    ext F
    apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The diagonal nerve of the exact-row groupoid reassembles into the original grid model. -/
def fromRowDiagonal : TheoremA.diagonalSSet (rowNerve E) ⟶
    sSet E.inflation (MorphismProperty.isomorphisms C) where
  app _ := ↾fun G ↦ ⟨rowsGrid E G, rowsGrid_isSimplex E G⟩
  naturality n m α := by
    ext G
    rfl

/-- This identifies the genuine existing S-model with its exact-row groupoid presentation. -/
def rowDiagonalIso : sSet E.inflation (MorphismProperty.isomorphisms C) ≅
    TheoremA.diagonalSSet (rowNerve E) where
  hom := toRowDiagonal E
  inv := fromRowDiagonal E
  hom_inv_id := by
    ext n F
    apply Subtype.ext
    exact rowsGrid_gridRows E F.2
  inv_hom_id := by
    ext n G
    exact gridRows_rowsGrid E G

end Quillen.Waldhausen.QuillenComparison
