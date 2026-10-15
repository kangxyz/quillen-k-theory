/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.QuillenComparison.RowBase
public import Quillen.Waldhausen.QuillenComparison.ReconstructedSpan

/-! # Every finite Q-chain comes from an actual exact S-row

The proof inducts on chain length. A representative of the new final
Q-arrow pulls back the preceding admissible flag, and adjoining zero and
the new target gives the next exact row. The previously proved terminal
span identity verifies the actual comparison, not just object counts.
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

/-- Every finite Q-chain has a genuine exact-row preimage up to chain isomorphism. -/
theorem exists_row_of_chain (n : ℕ) (G : ComposableArrows (Q E.deflation E.inflation) n) :
    ∃ F : Row E (Edgewise.ε.obj ⦋n⦌),
      Nonempty (((rowChainComparison E ⦋n⦌).obj F).of ≅ G) := by
  induction n with
  | zero => exact ⟨objectRow E (G.obj 0).obj.of, ⟨objectRowChainIso E G⟩⟩
  | succ n ih =>
    obtain ⟨F, ⟨e⟩⟩ := ih (Fin.castSuccFunctor (n + 1) ⋙ G)
    let a := (E.qIsoOfIso (centralTopIso E F)).symm ≪≫ e.app (Fin.last n)
    let f := a.hom ≫ G.map' n (n + 1)
    obtain ⟨s, hs⟩ := Quotient.exists_rep f
    change Span E.deflation E.inflation
      ((initialFlag E F).obj (Fin.last (Edgewise.ε.obj ⦋n⦌).len))
      (G.obj (Fin.last (n + 1))).obj.of at s
    change Q.mkHom E.deflation E.inflation s = f at hs
    let R := reconstructedRow E F s.l s.wl s.r s.wr
    let β := reconstructedInitialChainIso E F s.l s.wl s.r s.wr ≪≫ e
    let α := E.qIsoOfIso (reconstructedTopIso E F s.l s.wl s.r s.wr)
    refine ⟨R, ⟨chainIsoMkLast β α ?_⟩⟩
    change ((rowChainComparison E ⦋n + 1⦌).obj R).of.map' n (n + 1) ≫ α.hom =
      (β.app (Fin.last n)).hom ≫ G.map' n (n + 1)
    dsimp only [R, α]
    rw [reconstructedRow_last_step]
    change _ ≫ _ ≫ Q.mkHom E.deflation E.inflation s = _
    rw [hs]
    simp only [f, a, β, Iso.app_hom, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Category.assoc, Iso.hom_inv_id_assoc]

/-- Essential surjectivity of the prescribed central-interval comparison. -/
instance rowChainComparison_essSurj (n : SimplexCategory) : (rowChainComparison E n).EssSurj where
  mem_essImage G := by
    obtain ⟨F, ⟨e⟩⟩ := exists_row_of_chain E n.len G.of
    exact ⟨F, ⟨Core.isoMk e⟩⟩

/-- Fullness, faithfulness and reconstruction give the actual row equivalence. -/
instance rowChainComparison_isEquivalence (n : SimplexCategory) :
    (rowChainComparison E n).IsEquivalence where

/-- The equivalence retains exactly the original central-interval functor. -/
def rowChainEquivalence (n : SimplexCategory) :
    Row E (Edgewise.ε.obj n) ≌ Core (ComposableArrows (Q E.deflation E.inflation) n.len) :=
  (rowChainComparison E n).asEquivalence

end Quillen.Waldhausen.QuillenComparison
