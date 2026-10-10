/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.CategoryTheory.Iso

/-!
# A rectangular model of the classification diagonal

An n-simplex is a square ordinal diagram whose vertical arrows are
isomorphisms. Diagonal evaluation maps it to the ordinary nerve, and
constant vertical diagrams give a strict section.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite
open scoped Simplicial
universe u v

namespace Quillen.Classification

/-- A separate wrapper fixes the preorder category on the rectangular grid. -/
def Grid (n : SimplexCategory) := Fin (n.len + 1) × Fin (n.len + 1)

instance (n : SimplexCategory) : PartialOrder (Grid n) :=
  inferInstanceAs (PartialOrder (Fin (n.len + 1) × Fin (n.len + 1)))

/-- Simultaneous reindexing of the vertical and horizontal coordinates. -/
def gridMap {m n : SimplexCategory} (α : m ⟶ n) : Grid m ⥤ Grid n :=
  (show Monotone (fun p : Grid m ↦ (α.toOrderHom p.1, α.toOrderHom p.2)) from
    fun _ _ h ↦ ⟨α.toOrderHom.monotone h.1, α.toOrderHom.monotone h.2⟩).functor

/-- The diagonal functor from the ordinal vertex category into the square grid, sending `i` to
`(i, i)`. -/
def diagonal (n : SimplexCategory) : Fin (n.len + 1) ⥤ Grid n :=
  (show Monotone (fun i : Fin (n.len + 1) ↦ ((i, i) : Grid n)) from
    fun _ _ h ↦ ⟨h, h⟩).functor

/-- The second-coordinate projection from the square grid to the ordinal vertex category. -/
def second (n : SimplexCategory) : Grid n ⥤ Fin (n.len + 1) :=
  (show Monotone (fun p : Grid n ↦ p.2) from fun _ _ h ↦ h.2).functor

variable {D : Type u} [Category.{v} D] {n : SimplexCategory}

/-- Only arrows in the first, vertical coordinate must be isomorphisms. -/
def IsVerticalIso (F : Grid n ⥤ D) : Prop :=
  ∀ (s t i : Fin (n.len + 1)) (hst : s ≤ t),
    IsIso (F.map (homOfLE (show (s, i) ≤ (t, i) from ⟨hst, le_rfl⟩)))

theorem IsVerticalIso.precomp {m : SimplexCategory} {F : Grid n ⥤ D}
    (hF : IsVerticalIso F) (α : m ⟶ n) : IsVerticalIso (gridMap α ⋙ F) :=
  fun _ _ _ h ↦ hF _ _ _ (α.toOrderHom.monotone h)

/-- The diagonal classification simplicial set in the rectangular-grid model. -/
def sSet (D : Type u) [Category.{v} D] : SSet.{max u v} where
  obj n := { F : Grid n.unop ⥤ D // IsVerticalIso F }
  map α := ↾fun F ↦ ⟨gridMap α.unop ⋙ F.1, F.2.precomp α.unop⟩
  map_id n := by ext F; rfl
  map_comp α β := by ext F; rfl

/-- Natural diagonal evaluation retains both diagram directions. -/
def evaluation (D : Type u) [Category.{v} D] : sSet D ⟶ nerve D where
  app n := ↾fun F ↦ diagonal n.unop ⋙ F.1
  naturality _ _ _ := by ext F; rfl

/-- A nerve chain gives a diagram constant in its vertical coordinate. -/
def constant (D : Type u) [Category.{v} D] : nerve D ⟶ sSet D where
  app n := ↾fun F ↦ ⟨second n.unop ⋙ F, fun s t i h ↦ by
    change IsIso (F.map (𝟙 i))
    rw [F.map_id]
    infer_instance⟩
  naturality _ _ _ := by ext F; rfl

@[simp]
theorem constant_evaluation (D : Type u) [Category.{v} D] :
    constant D ≫ evaluation D = 𝟙 (nerve D) := by ext n F; rfl

/-- Actual vertical arrows, before extending them by inversion. -/
def verticalMap (F : Grid n ⥤ D) (s t i : Fin (n.len + 1)) (h : s ≤ t) :
    F.obj (s, i) ⟶ F.obj (t, i) := F.map (homOfLE ⟨h, le_rfl⟩)

@[simp]
theorem verticalMap_id (F : Grid n ⥤ D) (s i : Fin (n.len + 1)) :
    verticalMap F s s i le_rfl = 𝟙 _ := F.map_id _

@[reassoc (attr := simp)]
theorem verticalMap_comp (F : Grid n ⥤ D) (s t r i : Fin (n.len + 1))
    (hst : s ≤ t) (htr : t ≤ r) :
    verticalMap F s t i hst ≫ verticalMap F t r i htr =
      verticalMap F s r i (hst.trans htr) := by
  simp only [verticalMap, ← F.map_comp]
  rfl

/-- Coherent transport between any two rows, through their common initial row. -/
def transport (F : Grid n ⥤ D) (hF : IsVerticalIso F)
    (s t i : Fin (n.len + 1)) : F.obj (s, i) ≅ F.obj (t, i) := by
  haveI : IsIso (verticalMap F 0 s i (Fin.zero_le _)) := hF 0 s i (Fin.zero_le _)
  haveI : IsIso (verticalMap F 0 t i (Fin.zero_le _)) := hF 0 t i (Fin.zero_le _)
  exact (asIso (verticalMap F 0 s i (Fin.zero_le _))).symm ≪≫
    asIso (verticalMap F 0 t i (Fin.zero_le _))

@[simp]
theorem transport_self (F : Grid n ⥤ D) (hF : IsVerticalIso F)
    (s i : Fin (n.len + 1)) : transport F hF s s i = Iso.refl _ := by
  simp [transport]

@[simp]
theorem transport_trans (F : Grid n ⥤ D) (hF : IsVerticalIso F)
    (s t r i : Fin (n.len + 1)) :
    transport F hF s t i ≪≫ transport F hF t r i = transport F hF s r i := by
  simp [transport]

/-- On an ordered pair, transport is the original diagram arrow. -/
theorem transport_hom_of_le (F : Grid n ⥤ D) (hF : IsVerticalIso F)
    (s t i : Fin (n.len + 1)) (hst : s ≤ t) :
    (transport F hF s t i).hom = verticalMap F s t i hst := by
  have : IsIso (verticalMap F 0 s i (Fin.zero_le _)) := hF 0 s i (Fin.zero_le _)
  change inv (verticalMap F 0 s i (Fin.zero_le _)) ≫ verticalMap F 0 t i (Fin.zero_le _) = _
  rw [← verticalMap_comp F 0 s t i (Fin.zero_le _) hst]
  simp

/-- Reindexing preserves transport even when an ordinal map identifies rows. -/
theorem transport_precomp {m : SimplexCategory} (F : Grid n ⥤ D)
    (hF : IsVerticalIso F) (α : m ⟶ n) (s t i : Fin (m.len + 1)) :
    (transport (gridMap α ⋙ F) (hF.precomp α) s t i).hom =
      (transport F hF (α.toOrderHom s) (α.toOrderHom t) (α.toOrderHom i)).hom := by
  rcases le_total s t with h | h
  · rw [transport_hom_of_le _ _ _ _ _ h,
      transport_hom_of_le _ _ _ _ _ (α.toOrderHom.monotone h)]
    rfl
  · have hh := transport_hom_of_le (gridMap α ⋙ F) (hF.precomp α) t s i h
    have hh' := transport_hom_of_le F hF (α.toOrderHom t) (α.toOrderHom s)
      (α.toOrderHom i) (α.toOrderHom.monotone h)
    have hi : transport (gridMap α ⋙ F) (hF.precomp α) t s i =
        transport F hF (α.toOrderHom t) (α.toOrderHom s) (α.toOrderHom i) :=
      Iso.ext (hh.trans hh'.symm)
    have hinv := congrArg (fun e ↦ e.symm.hom) hi
    simpa [transport] using hinv

end Quillen.Classification
