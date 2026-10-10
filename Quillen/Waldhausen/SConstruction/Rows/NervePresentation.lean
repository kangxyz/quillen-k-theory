/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Waldhausen.SConstruction.Rows.NerveBridge

/-! # The actual weak-row nerve presents the original bisimplicial S-construction

The original-grid simplex equivalence commutes with both ordinal directions.
Its diagonal therefore presents the existing Waldhausen simplicial set by
actual fine-weak quotient-row categories, without replacing any map.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen.QuotientRows
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- Original ordinal restriction on the actual pointwise weak-row category. -/
def weakRowsReindex {m n : SimplexCategory} (α : m ⟶ n) : WeakRows W n ⥤ WeakRows W m where
  obj X := ⟨(reindex W α).obj X.obj⟩
  map f := ⟨(reindex W α).map f.hom, (reindex_exact W α).weak f.hom f.property⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Both original coordinates commute with the unchanged grid-to-chain construction. -/
theorem gridToWeakChain_reindex {n n' k k' : SimplexCategory}
    (α : n' ⟶ n) (β : k' ⟶ k) (F : Grid₂ n k ⥤ C) (hF : IsSimplex₂ W.cof W.weq F) :
    gridToWeakChain W (gridMap₂ α β ⋙ F) (hF.precomp W.cof W.weq α β) =
      (SimplexCategory.toCat.map β).toFunctor ⋙ gridToWeakChain W F hF ⋙ weakRowsReindex W α := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The actual weak-row categories, contravariant in the original interval degree. -/
def weakRowCategories : SimplexCategoryᵒᵖ ⥤ Cat.{v,max u v} where
  obj n := Cat.of (WeakRows W n.unop)
  map α := Cat.Hom.ofFunctor (weakRowsReindex W α.unop)
  map_id _ := by apply Cat.Hom.ext; apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
  map_comp _ _ := by apply Cat.Hom.ext; apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The genuine nerve in the second direction, retaining the actual weak maps. -/
def weakRowNerve : SimplexCategoryᵒᵖ ⥤ SSet.{max u v} := weakRowCategories W ⋙ nerveFunctor

/-- The original S-grid and the actual weak-row nerve are isomorphic as bisimplicial sets. -/
def gridNerveIso : bisimplicialSSet W ≅ weakRowNerve W :=
  NatIso.ofComponents (fun n ↦ NatIso.ofComponents
    (fun k ↦ Equiv.toIso (gridWeakChainEquiv W n.unop k.unop)) (by
      intro k l β
      ext F : 3
      apply CategoryTheory.Functor.ext (fun _ ↦ rfl))) (by
    intro n m α
    ext k F : 4
    apply CategoryTheory.Functor.ext (fun _ ↦ rfl))

/-- Forward simplices retain every original grid component. -/
@[simp] theorem gridNerveIso_hom_component (n k : SimplexCategory)
    (F : Grid₂ n k ⥤ C) (hF : IsSimplex₂ W.cof W.weq F)
    (t : Fin (k.len + 1)) (p : Interval n) :
    (((((gridNerveIso W).hom.app (op n)).app (op k) ⟨F,hF⟩).obj t).obj.obj.obj p) =
      F.obj (t,p) := rfl

/-- The inverse is exactly the original weak-chain reconstruction, on every grid arrow. -/
@[simp] theorem gridNerveIso_inv_val (n k : SimplexCategory)
    (F : ComposableArrows (WeakRows W n) k.len) :
    ((((gridNerveIso W).inv.app (op n)).app (op k) F).val) = weakChainToGrid W F := rfl

/-- The original Waldhausen simplicial set is the diagonal of the actual weak-row nerve. -/
def sSetWeakRowDiagonalIso : sSet W.cof W.weq ≅ TheoremA.diagonalSSet (weakRowNerve W) :=
  (bisimplicialDiagonalIso W).symm ≪≫ TheoremA.diagonalFunctor.mapIso (gridNerveIso W)

/-- The prescribed original diagonal map is still the unchanged grid-to-weak-chain map. -/
@[simp] theorem sSetWeakRowDiagonalIso_hom_app (n : SimplexCategory)
    (F : (sSet W.cof W.weq).obj (op n)) :
    (sSetWeakRowDiagonalIso W).hom.app (op n) F =
      gridToWeakChain W F.val ((isSimplex₂_diagonal_iff W.cof W.weq F.val).2 F.property) := rfl

end Quillen.Waldhausen.QuotientRows
