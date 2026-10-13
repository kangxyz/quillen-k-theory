/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.Fibration.CanonicalFiberMap
public import Quillen.Waldhausen.SConstruction.BisimplexRealization
public import Quillen.Waldhausen.GrothendieckComparison.WeakRelations

/-! # Original change of weakness on entire bisimplex families

The original localization map retains the full fine grid and both realization coordinates.
This is the precise comparison used for the fine weak projection of a scalar factorization.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Convexity MonoidalCategory
open scoped Simplicial Topology
universe u v
namespace Quillen.Waldhausen.Fibration
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) {n m : ℕ}
  (F : Grid₂ ⦋n⦌ ⦋m⦌ ⥤ C) (hF : IsSimplex₂ V.cof V.weq F)
  (hG : IsSimplex₂ N.coarse.cof N.coarse.weq F)

/-- The original change-of-weak-equivalence map leaves the entire fine grid unchanged. -/
theorem bisimplexFamily_changeWeak :
    bisimplexFamily V F hF ≫ sSetMap (changeWeak_exact N) =
      bisimplexFamily N.coarse F hG := by
  ext k z
  apply Subtype.ext
  exact Functor.comp_id _

/-- Both original barycentric coordinates survive the actual localization map. -/
theorem bisimplexRealization_changeWeak
    (z : StdSimplex ℝ (Fin (n + 1))) (t : StdSimplex ℝ (Fin (m + 1))) :
    changeWeakMap N (bisimplexRealization V F hF (z, t)) =
      bisimplexRealization N.coarse F hG (z, t) := by
  change (SSet.toTop.map (bisimplexFamily V F hF) ≫
    SSet.toTop.map (sSetMap (changeWeak_exact N)))
      ((realizationProductSimplexHomeomorph n m).symm (z, t)) = _
  rw [← Functor.map_comp, bisimplexFamily_changeWeak N F hF hG]
  rfl

/-- The original weak-arrow grid depends on the chosen zero, but not its weakness certificate. -/
theorem weakObjectSimplex_val_of_zero_eq (W : Structure C) (h0 : V.zero = W.zero)
    {A B : C} (f : A ⟶ B) (hf : V.weq f) (hg : W.weq f) :
    (V.weakObjectSimplex f hf).val = (W.weakObjectSimplex f hg).val := by
  cases V
  cases W
  cases h0
  refine CategoryTheory.Functor.ext (fun p ↦ ?_) ?_
  · rcases p with ⟨s, p⟩
    fin_cases s <;> rfl
  · rintro ⟨s, p⟩ ⟨t, q⟩ a
    fin_cases s <;> fin_cases t <;>
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id] <;>
      first | rfl | exact False.elim (by have h := (leOfHom a).1; simp at h)

/-- The entire fine weak-arrow square is retained through the original localization map. -/
theorem weakObjectSquare_changeWeak {A B : C} (f : A ⟶ B) (hf : V.weq f)
    (t z : StdSimplex ℝ (Fin 2)) :
    changeWeakMap N (bisimplexRealization V (V.weakObjectSimplex f hf).val
      ((isSimplex₂_diagonal_iff _ _ _).mpr (V.weakObjectSimplex f hf).property) (t, z)) =
      bisimplexRealization N.coarse (N.coarse.weakObjectSimplex f (N.le_weq _ hf)).val
        ((isSimplex₂_diagonal_iff _ _ _).mpr
          (N.coarse.weakObjectSimplex f (N.le_weq _ hf)).property) (t, z) := by
  have he := weakObjectSimplex_val_of_zero_eq N.coarse N.zero_eq.symm f hf (N.le_weq _ hf)
  have hc : IsSimplex₂ N.coarse.cof N.coarse.weq (V.weakObjectSimplex f hf).val := by
    rw [he]
    exact (isSimplex₂_diagonal_iff _ _ _).mpr
      (N.coarse.weakObjectSimplex f (N.le_weq _ hf)).property
  rw [bisimplexRealization_changeWeak N _ _ hc]
  exact DFunLike.congr_fun (bisimplexRealization_congr N.coarse _ hc _ he) (t, z)

end Quillen.Waldhausen.Fibration
