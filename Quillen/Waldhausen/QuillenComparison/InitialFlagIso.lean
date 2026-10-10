/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Waldhausen.QuillenComparison.InitialFlag
public import Quillen.Waldhausen.QuillenComparison.RowFaithful

/-! # Exact row isomorphisms from compatible initial subobjects -/
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
variable {n : SimplexCategory}

@[simp]
theorem initialQuotient_initial (F : Row E n) (i : Fin (n.len + 1)) :
    initialQuotient E F (interval 0 i (Fin.zero_le _)) = 𝟙 _ := F.diagram.map_id _

/-- Cokernel extension agrees with the originally prescribed initial-flag components. -/
@[simp]
theorem extendFlagIso_initial {F G : Row E n} (e : initialFlag E F ≅ initialFlag E G)
    (i : Fin (n.len + 1)) :
    (extendFlagIso E e).hom.app (interval 0 i (Fin.zero_le _)) = e.hom.app i := by
  have h := initialQuotient_flagIsoAt E e (interval 0 i (Fin.zero_le _))
  simp only [initialQuotient_initial, Category.id_comp, Category.comp_id] at h
  exact h

/-- Cokernel extension is the unique row isomorphism agreeing on the initial flag. -/
theorem extendFlagIso_unique {F G : Row E n} (e : initialFlag E F ≅ initialFlag E G)
    (f : F ⟶ G) (hf : ∀ i, f.hom.app (interval 0 i (Fin.zero_le _)) = e.hom.app i) :
    f = extendFlagIso E e := by
  apply Iso.ext
  apply rowNatTrans_ext_top E
  rw [extendFlagIso_initial, hf]

/-- Compatible isomorphisms of all initial subobjects are automatically natural:
the map into the top initial object is monic. -/
def initialFlagIsoOfTop {F G : Row E n}
    (e : ∀ i, (initialFlag E F).obj i ≅ (initialFlag E G).obj i)
    (h : ∀ i, (initialFlag E F).map (homOfLE (Fin.le_last i)) ≫ (e (Fin.last n.len)).hom =
      (e i).hom ≫ (initialFlag E G).map (homOfLE (Fin.le_last i))) :
    initialFlag E F ≅ initialFlag E G :=
  NatIso.ofComponents e (by
    intro i j f
    let : Mono ((initialFlag E G).map (homOfLE (Fin.le_last j))) :=
      E.mono_of_inflation (G.simplex.cofibration 0 0 j (Fin.last n.len) (Fin.zero_le _)
        (Fin.le_last j))
    apply (cancel_mono ((initialFlag E G).map (homOfLE (Fin.le_last j)))).1
    rw [Category.assoc, ← h j, ← Category.assoc, ← CategoryTheory.Functor.map_comp]
    rw [Category.assoc, ← CategoryTheory.Functor.map_comp]
    exact h i)

/-- Existence of compatible initial-subobject isomorphisms suffices to recover
a whole-row isomorphism, using actual monicity and cokernel universal properties. -/
def rowIsoOfInitialSubobjects {F G : Row E n}
    (e : ∀ i, (initialFlag E F).obj i ≅ (initialFlag E G).obj i)
    (h : ∀ i, (initialFlag E F).map (homOfLE (Fin.le_last i)) ≫ (e (Fin.last n.len)).hom =
      (e i).hom ≫ (initialFlag E G).map (homOfLE (Fin.le_last i))) : F ⟶ G :=
  extendFlagIso E (initialFlagIsoOfTop E e h)

end Quillen.Waldhausen.QuillenComparison
