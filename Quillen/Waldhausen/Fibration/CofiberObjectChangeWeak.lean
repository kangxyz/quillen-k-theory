/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.Fibration.CanonicalFiberMap
public import Quillen.Waldhausen.GrothendieckComparison.CofiberObjectTrack

/-! # The original fine cofiber track through the localization map -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial Topology
universe u v
namespace Quillen.Waldhausen.Fibration
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {V : Structure C} (N : NestedWeakEquivalences V)
  {A B Q : C} (i : A ⟶ B) (q : B ⟶ Q)
  (hi : V.cof i) (hi' : N.coarse.cof i)
  (hQ : IsPushout i (0 : A ⟶ V.zero) q (0 : V.zero ⟶ Q))
  (hQ' : IsPushout i (0 : A ⟶ N.coarse.zero) q (0 : N.coarse.zero ⟶ Q))

/-- With the same specified zero, the genuine cofiber triangle keeps every original grid map. -/
theorem cofiberObjectSimplex_val_of_zero_eq
    (W : Structure C) (h0 : V.zero = W.zero) (hw : W.cof i)
    (hW : IsPushout i (0 : A ⟶ W.zero) q (0 : W.zero ⟶ Q)) :
    (V.cofiberObjectSimplex i q hi hQ).val = (W.cofiberObjectSimplex i q hw hW).val := by
  cases V
  cases W
  cases h0
  rfl

/-- The unchanged localization simplicial map sends the actual fine triangle to its coarse one. -/
theorem cofiberObjectSimplex_changeWeak :
    (sSetMap (changeWeak_exact N)).app (op ⦋2⦌) (V.cofiberObjectSimplex i q hi hQ) =
      N.coarse.cofiberObjectSimplex i q hi' hQ' := by
  apply Subtype.ext
  change (V.cofiberObjectSimplex i q hi hQ).val ⋙ 𝟭 C = _
  rw [Functor.comp_id]
  exact cofiberObjectSimplex_val_of_zero_eq i q hi hQ N.coarse N.zero_eq.symm hi' hQ'

/-- The entire original triangle homotopy retains both comparison and object-loop time. -/
theorem cofiberObjectLoopTrack_changeWeak (r t : unitInterval) :
    changeWeakMap N (V.cofiberObjectLoopTrack i q hi hQ (r, t)) =
      N.coarse.cofiberObjectLoopTrack i q hi' hQ' (r, t) := by
  rw [Structure.cofiberObjectLoopTrack_apply, Structure.cofiberObjectLoopTrack_apply,
    realizationEdgeCompositionHomotopy_apply, realizationEdgeCompositionHomotopy_apply]
  change (SSet.toTop.map (SSet.yonedaEquiv.symm (V.cofiberObjectSimplex i q hi hQ)) ≫
    SSet.toTop.map (sSetMap (changeWeak_exact N))) _ = _
  rw [← Functor.map_comp, SSet.yonedaEquiv_symm_comp,
    cofiberObjectSimplex_changeWeak N i q hi hi' hQ hQ']
  rfl

end Quillen.Waldhausen.Fibration
