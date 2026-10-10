/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Waldhausen.Approximation.WeakRowSimplicial
public import Quillen.Waldhausen.Functor
public import Quillen.Waldhausen.QuillenComparison.RowDiagonal

/-! # The original weak-equivalence grid is the diagonal of the actual row nerve -/
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
variable (E : Quillen.ExactStructure C) (cof weq : MorphismProperty C)
  [weq.IsMultiplicative] (hcof : cof ≤ E.inflation)
variable {n : SimplexCategory} {F : Grid n ⥤ C}
variable (hF : IsSimplex cof weq F)

/-- Extract an actual exact quotient row from the original diagonal simplex. -/
def weakGridRow (t : Fin (n.len + 1)) : WeakRow E cof weq n where
  row := {
    diagram := rowRestriction t ⋙ F
    simplex := {
      zero := fun _ i ↦ hF.zero t i
      cofibration := fun _ i j k hij hjk ↦ hcof _ (hF.cofibration t i j k hij hjk)
      quotient := fun _ i j k hij hjk ↦ hF.quotient t i j k hij hjk
      weak := by
        intro s u i j hsu hij
        change IsIso (F.map (𝟙 _))
        rw [F.map_id]
        infer_instance } }
  cofibration := hF.cofibration t

/-- Actual vertical weak equivalences form natural transformations of rows. -/
def weakGridRowMap (s t : Fin (n.len + 1)) (hst : s ≤ t) :
    weakGridRow E cof weq hcof hF s ⟶ weakGridRow E cof weq hcof hF t :=
  ⟨{ app := fun p ↦ verticalMap (F := F) s t hst p.2
     naturality := by
       intro p q f
       exact rowMap_verticalMap s t hst p.2 q.2 (leOfHom f).1 (leOfHom f).2 },
    fun p ↦ hF.weak s t p.1.1 p.1.2 hst p.2⟩

/-- Reorganize an original grid simplex as a chain in the weak-equivalence row category. -/
def weakGridRows : ComposableArrows (WeakRow E cof weq n) n.len where
  obj := weakGridRow E cof weq hcof hF
  map f := weakGridRowMap E cof weq hcof hF _ _ (leOfHom f)
  map_id t := by
    apply Subtype.ext
    ext p
    exact F.map_id _
  map_comp f g := by
    apply Subtype.ext
    ext p
    exact F.map_comp _ _

/-- Reassemble a chain of exact rows into the actual two-direction grid. -/
def weakRowsGrid (G : ComposableArrows (WeakRow E cof weq n) n.len) : Grid n ⥤ C where
  obj p := (G.obj p.1).row.diagram.obj p.2
  map {p q} f := (G.map (homOfLE (leOfHom f).1)).val.app p.2 ≫
    (G.obj q.1).row.diagram.map (homOfLE (leOfHom f).2)
  map_id p := by
    rcases p with ⟨t, p⟩
    change (G.map (𝟙 t)).val.app p ≫ (G.obj t).row.diagram.map (𝟙 p) = _
    rw [G.map_id, (G.obj t).row.diagram.map_id]
    exact Category.id_comp _
  map_comp {p q r} f g := by
    rcases p with ⟨s, p⟩
    rcases q with ⟨t, q⟩
    rcases r with ⟨u, r⟩
    change (G.map ((homOfLE (leOfHom f).1) ≫ (homOfLE (leOfHom g).1))).val.app p ≫
      (G.obj u).row.diagram.map ((homOfLE (leOfHom f).2) ≫ (homOfLE (leOfHom g).2)) = _
    rw [G.map_comp, (G.obj u).row.diagram.map_comp]
    change (_ ≫ _) ≫ (_ ≫ _) = (_ ≫ _) ≫ (_ ≫ _)
    simp only [Category.assoc]
    congr 1
    rw [← (G.map (homOfLE (leOfHom g).1)).val.naturality_assoc]

/-- Reassembly retains zero diagonals, cofibrations, quotient pushouts and
actual vertical weak equivalences. -/
theorem weakRowsGrid_isSimplex (G : ComposableArrows (WeakRow E cof weq n) n.len) :
    IsSimplex cof weq (weakRowsGrid E cof weq G) where
  zero t i := (G.obj t).row.simplex.zero 0 i
  cofibration t i j k hij hjk := by
    change cof ((G.map (𝟙 t)).val.app _ ≫ (G.obj t).row.diagram.map _)
    rw [G.map_id]
    change cof (𝟙 _ ≫ (G.obj t).row.diagram.map _)
    rw [Category.id_comp]
    exact (G.obj t).cofibration i j k hij hjk
  quotient t i j k hij hjk := by
    change IsPushout ((G.map (𝟙 t)).val.app _ ≫ (G.obj t).row.diagram.map _)
      ((G.map (𝟙 t)).val.app _ ≫ (G.obj t).row.diagram.map _)
      ((G.map (𝟙 t)).val.app _ ≫ (G.obj t).row.diagram.map _)
      ((G.map (𝟙 t)).val.app _ ≫ (G.obj t).row.diagram.map _)
    rw [G.map_id]
    change IsPushout (𝟙 _ ≫ (G.obj t).row.diagram.map _) (𝟙 _ ≫ (G.obj t).row.diagram.map _)
      (𝟙 _ ≫ (G.obj t).row.diagram.map _) (𝟙 _ ≫ (G.obj t).row.diagram.map _)
    simp only [Category.id_comp]
    exact (G.obj t).row.simplex.quotient 0 i j k hij hjk
  weak s t i j hst hij := by
    change weq ((G.map (homOfLE hst)).val.app _ ≫
      (G.obj t).row.diagram.map (𝟙 _))
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
    exact (G.map (homOfLE hst)).property _

/-- Extracting and reassembling the rows retains the original grid functor. -/
@[simp]
theorem weakRowsGrid_weakGridRows : weakRowsGrid E cof weq (weakGridRows E cof weq hcof hF) = F
    := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro p q f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact (F.map_comp _ _).symm

@[simp]
theorem weakRow_eqToHom_app {F G : WeakRow E cof weq n} (h : F = G) (p : Interval n) :
    (eqToHom h : F ⟶ G).val.app p = eqToHom (congrArg (fun R : WeakRow E cof weq n ↦
      R.row.diagram.obj p) h) := by
  cases h
  rfl

/-- Reassembly and extraction retain the original chain of row weak equivalences. -/
@[simp]
theorem weakGridRows_weakRowsGrid (G : ComposableArrows (WeakRow E cof weq n) n.len) :
    weakGridRows E cof weq hcof (weakRowsGrid_isSimplex E cof weq G) = G := by
  have hobj (t : Fin (n.len + 1)) : weakGridRow E cof weq hcof (weakRowsGrid_isSimplex E cof weq
    G) t = G.obj t := by
    apply WeakRow.ext
    apply Row.ext
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
    intro p q f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change (G.map (𝟙 t)).val.app p ≫ (G.obj t).row.diagram.map f = _
    rw [G.map_id]
    exact Category.id_comp _
  refine CategoryTheory.Functor.ext hobj ?_
  intro s t f
  apply Subtype.ext
  ext p
  change _ = (eqToHom (hobj s) : _ ⟶ _).val.app p ≫ (G.map f).val.app p ≫
    (eqToHom (hobj t).symm : _ ⟶ _).val.app p
  simp only [weakRow_eqToHom_app, eqToHom_refl, Category.id_comp, Category.comp_id]
  change (G.map f).val.app p ≫ (G.obj t).row.diagram.map (𝟙 p) = _
  rw [(G.obj t).row.diagram.map_id, Category.comp_id]

/-- The original S-grid simplicial set maps to the diagonal of the weak-equivalence row nerve. -/
def toWeakRowDiagonal : sSet cof weq ⟶
    TheoremA.diagonalSSet (weakRowNerve E cof weq) where
  app _ := ↾fun F ↦ weakGridRows E cof weq hcof F.2
  naturality n m α := by
    ext F
    apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The diagonal nerve of the weak-equivalence row category reassembles into the original grid
model. -/
def fromWeakRowDiagonal : TheoremA.diagonalSSet (weakRowNerve E cof weq) ⟶
    sSet cof weq where
  app _ := ↾fun G ↦ ⟨weakRowsGrid E cof weq G, weakRowsGrid_isSimplex E cof weq G⟩
  naturality n m α := by
    ext G
    rfl

/-- This identifies the genuine existing S-model with its weak-equivalence row category
presentation. -/
def weakRowDiagonalIso : sSet cof weq ≅
    TheoremA.diagonalSSet (weakRowNerve E cof weq) where
  hom := toWeakRowDiagonal E cof weq hcof
  inv := fromWeakRowDiagonal E cof weq
  hom_inv_id := by
    ext n F
    apply Subtype.ext
    exact weakRowsGrid_weakGridRows E cof weq hcof F.2
  inv_hom_id := by
    ext n G
    exact weakGridRows_weakRowsGrid E cof weq hcof G


/-- The identification with genuine grids retains the canonical inclusion
when the cofibration convention is enlarged. -/
theorem weakRowDiagonalIso_inclusion (cof' : MorphismProperty C)
    (hcof' : cof' ≤ E.inflation) (h : cof ≤ cof')
    (hF : IsExact cof weq cof' weq (𝟭 C)) :
    sSetMap hF ≫ (weakRowDiagonalIso E cof' weq hcof').hom =
      (weakRowDiagonalIso E cof weq hcof).hom ≫
        TheoremA.diagonalMap (weakRowNerveInclusion E cof weq cof' h) := by
  ext n F
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- Reassembly of the canonical diagonal inclusion is precisely the original
S-construction map, including its unchanged weak equivalences. -/
theorem weakRowDiagonalIso_inclusion_reassembled (cof' : MorphismProperty C)
    (hcof' : cof' ≤ E.inflation) (h : cof ≤ cof')
    (hF : IsExact cof weq cof' weq (𝟭 C)) :
    (weakRowDiagonalIso E cof weq hcof).hom ≫
        TheoremA.diagonalMap (weakRowNerveInclusion E cof weq cof' h) ≫
          (weakRowDiagonalIso E cof' weq hcof').inv = sSetMap hF := by
  rw [← Category.assoc, ← weakRowDiagonalIso_inclusion E cof weq hcof cof' hcof' h hF]
  simp

end Quillen.Waldhausen
