/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.QuillenComparison.IntervalSpans
public import Quillen.CategoryTheory.QConstruction.SpanIsoNaturality

/-! # The vertical isomorphisms in the Q/S comparison -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe v u

namespace Quillen.Waldhausen.QuillenComparison

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : Quillen.ExactStructure C)
variable {n : SimplexCategory} {F : Grid n ⥤ C}
variable (hF : IsSimplex E.inflation (MorphismProperty.isomorphisms C) F)

/-- The actual map in the nerve direction, at a specified interval. -/
def verticalMap (s t : Fin (n.len + 1)) (hst : s ≤ t)
    {i j : Fin (n.len + 1)} (hij : i ≤ j) :
    F.obj (grid s i j hij) ⟶ F.obj (grid t i j hij) :=
  F.map (homOfLE (show grid s i j hij ≤ grid t i j hij from ⟨hst, le_rfl, le_rfl⟩))

/-- For the exact-category Waldhausen structure, these vertical maps really
are isomorphisms. -/
def verticalIso (s t : Fin (n.len + 1)) (hst : s ≤ t)
    {i j : Fin (n.len + 1)} (hij : i ≤ j) :
    F.obj (grid s i j hij) ≅ F.obj (grid t i j hij) := by
  letI : IsIso (verticalMap (F := F) s t hst hij) := hF.weak s t i j hst hij
  exact asIso (verticalMap (F := F) s t hst hij)

@[simp]
theorem verticalIso_hom (s t : Fin (n.len + 1)) (hst : s ≤ t)
    {i j : Fin (n.len + 1)} (hij : i ≤ j) :
    (verticalIso E hF s t hst hij).hom = verticalMap (F := F) s t hst hij := rfl

@[simp]
theorem verticalIso_id (s : Fin (n.len + 1)) {i j : Fin (n.len + 1)} (hij : i ≤ j) :
    verticalIso E hF s s le_rfl hij = Iso.refl _ := by
  apply Iso.ext
  exact F.map_id _

@[simp]
theorem verticalIso_comp (s t u : Fin (n.len + 1)) (hst : s ≤ t) (htu : t ≤ u)
    {i j : Fin (n.len + 1)} (hij : i ≤ j) :
    verticalIso E hF s t hst hij ≪≫ verticalIso E hF t u htu hij =
      verticalIso E hF s u (hst.trans htu) hij := by
  apply Iso.ext
  exact (F.map_comp _ _).symm

omit [Preadditive C] [HasFiniteBiproducts C] in
/-- The nerve and quotient directions commute in the original grid functor. -/
theorem rowMap_verticalMap (s t : Fin (n.len + 1)) (hst : s ≤ t)
    {i j k l : Fin (n.len + 1)} (hij : i ≤ j) (hkl : k ≤ l)
    (hik : i ≤ k) (hjl : j ≤ l) :
    rowMap (F := F) s hij hkl hik hjl ≫ verticalMap (F := F) s t hst hkl =
      verticalMap (F := F) s t hst hij ≫ rowMap (F := F) t hij hkl hik hjl := by
  simp only [rowMap, verticalMap, ← F.map_comp]
  congr 1

/-- Pointwise vertical isomorphisms induce the canonical natural
isomorphism between the interval-containment Q-functors. -/
def intervalQFunctorIso (s t : Fin (n.len + 1)) (hst : s ≤ t) :
    intervalQFunctor E hF s ≅ intervalQFunctor E hF t :=
  NatIso.ofComponents
    (fun p ↦ E.qIsoOfIso (verticalIso E hF s t hst p.endpoints)) (by
      intro p q f
      apply E.qSpan_iso_naturality
        (intervalSpan E hF s (leOfHom f)) (intervalSpan E hF t (leOfHom f))
        (verticalIso E hF s t hst p.endpoints)
        (verticalIso E hF s t hst q.endpoints)
        (verticalIso E hF s t hst ((NestedInterval.left_anti (leOfHom f)).trans p.endpoints))
      · exact rowMap_verticalMap s t hst _ _ (NestedInterval.left_anti (leOfHom f)) le_rfl
      · exact rowMap_verticalMap s t hst _ _ le_rfl (NestedInterval.right_mono (leOfHom f)))

/-- All rows and their actual vertical isomorphisms form a functor, so the
comparison uses the nerve direction rather than discarding it. -/
def rowsQFunctor : Fin (n.len + 1) ⥤ (NestedInterval n ⥤ Q E.deflation E.inflation) where
  obj t := intervalQFunctor E hF t
  map f := (intervalQFunctorIso E hF _ _ (leOfHom f)).hom
  map_id t := by
    ext p
    change (E.qIsoOfIso (verticalIso E hF t t le_rfl p.endpoints)).hom = 𝟙 _
    rw [verticalIso_id]
    rfl
  map_comp {s t u} f g := by
    ext p
    change (E.qIsoOfIso (verticalIso E hF s u _ p.endpoints)).hom =
      (E.qIsoOfIso (verticalIso E hF s t _ p.endpoints)).hom ≫
        (E.qIsoOfIso (verticalIso E hF t u _ p.endpoints)).hom
    rw [← Iso.trans_hom, ← ExactStructure.qIsoOfIso_trans, verticalIso_comp]

end Quillen.Waldhausen.QuillenComparison
