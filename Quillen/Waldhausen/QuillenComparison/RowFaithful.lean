/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.QuillenComparison.RowSimplicial
public import Quillen.CategoryTheory.QConstruction.Core

/-! # Faithfulness of the exact-row Q comparison

A natural transformation of exact quotient diagrams is determined by its
component on the whole interval. Monic inclusions determine the initial
subobjects, and epic quotient maps determine all remaining components.
The central-interval Q comparison therefore detects every row isomorphism.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe v u

namespace Quillen.Waldhausen.QuillenComparison

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : CategoryTheory.ExactCategory.ExactStructure C)
variable {n : SimplexCategory}

/-- A map of exact quotient rows is determined by its whole-interval component. -/
theorem rowNatTrans_ext_top {F G : Row E n} (e f : F.diagram ⟶ G.diagram)
    (h : e.app (interval 0 (Fin.last n.len) (Fin.zero_le _)) =
      f.app (interval 0 (Fin.last n.len) (Fin.zero_le _))) : e = f := by
  have h₀ (j : Fin (n.len + 1)) :
      e.app (interval 0 j (Fin.zero_le _)) = f.app (interval 0 j (Fin.zero_le _)) := by
    let g : interval 0 j (Fin.zero_le _) ⟶ interval 0 (Fin.last n.len) (Fin.zero_le _) :=
      homOfLE ⟨le_rfl, Fin.le_last j⟩
    let : Mono (G.diagram.map g) := E.mono_of_inflation
      (G.simplex.cofibration 0 0 j (Fin.last n.len) (Fin.zero_le _) (Fin.le_last j))
    apply (cancel_mono (G.diagram.map g)).1
    rw [← e.naturality, ← f.naturality, h]
  apply NatTrans.ext
  funext p
  rcases p with ⟨⟨i, j⟩, hij⟩
  let g : interval 0 j (Fin.zero_le _) ⟶ interval i j hij := homOfLE ⟨Fin.zero_le _, le_rfl⟩
  let : Epi (F.diagram.map g) := E.epi_of_deflation
    (row_deflation E F.simplex 0 0 i j (Fin.zero_le _) hij)
  apply (cancel_epi (F.diagram.map g)).1
  change F.diagram.map g ≫ e.app (interval i j hij) =
    F.diagram.map g ≫ f.app (interval i j hij)
  rw [e.naturality g, f.naturality g, h₀]

/-- The left endpoint of the last central interval is the original first vertex. -/
@[simp]
theorem lowerIndex_last (n : SimplexCategory) : lowerIndex n (Fin.last n.len) = 0 := by
  apply Fin.ext
  simp [lowerIndex, Edgewise.left]

/-- The right endpoint of the last central interval is the original last vertex. -/
@[simp]
theorem upperIndex_last (n : SimplexCategory) :
    upperIndex n (Fin.last n.len) = Fin.last (Edgewise.ε.obj n).len := by
  apply Fin.ext
  simp [upperIndex, Edgewise.right, Edgewise.ε, Edgewise.joinObj]
  omega

/-- The central interval comparison is faithful in every simplicial degree. -/
instance rowChainComparison_faithful (n : SimplexCategory) : (rowChainComparison E n).Faithful where
  map_injective {F G} e f h := by
    apply Iso.ext
    apply rowNatTrans_ext_top E
    have hq := congrArg (fun a ↦ a.iso.hom.app (Fin.last n.len)) h
    change (E.qIsoOfIso (e.app (interval (lowerIndex n (Fin.last n.len))
      (upperIndex n (Fin.last n.len)) _))).hom =
      (E.qIsoOfIso (f.app (interval (lowerIndex n (Fin.last n.len))
        (upperIndex n (Fin.last n.len)) _))).hom at hq
    have he := E.qIsoOfIso_injective (Iso.ext hq)
    have hh := congrArg Iso.hom he
    have hi : interval (lowerIndex n (Fin.last n.len)) (upperIndex n (Fin.last n.len))
        (lowerIndex_le_upperIndex n _ _) =
        interval 0 (Fin.last (Edgewise.ε.obj n).len) (Fin.zero_le _) :=
      Subtype.ext (Prod.ext (lowerIndex_last n) (upperIndex_last n))
    change e.hom.app _ = f.hom.app _ at hh
    rw [hi] at hh
    exact hh

end Quillen.Waldhausen.QuillenComparison
