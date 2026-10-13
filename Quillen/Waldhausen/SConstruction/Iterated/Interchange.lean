/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.Prespectrum
public import Quillen.Waldhausen.SConstruction.Rows.Interchange

/-!
# Actual higher-row interchange and cylinder compatibility

The genuine Reedy row transpose defines an isomorphism of exact zero-preserving models.
It is natural in original exact functors and ordinal restriction. Its compatibility with
the original one-step insertion keeps every underlying interval object and map, so the
higher cylinder maps are not replaced by unrelated choices.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS

/-- The genuine Reedy row transpose preserves the displayed zero row literally. -/
def rowSwap (W : Model.{u}) (m n : SimplexCategory) :
    (rows m).obj ((rows n).obj W) ≅ (rows n).obj ((rows m).obj W) where
  hom := ⟨QuotientRows.transposeRows W.waldhausen m n,
    QuotientRows.transposeRows_exact W.waldhausen m n, rfl⟩
  inv := ⟨QuotientRows.transposeRows W.waldhausen n m,
    QuotientRows.transposeRows_exact W.waldhausen n m, rfl⟩
  hom_inv_id := by apply Model.Hom.ext; exact QuotientRows.transposeRows_twice W.waldhausen m n
  inv_hom_id := by apply Model.Hom.ext; exact QuotientRows.transposeRows_twice W.waldhausen n m

/-- Actual row transpose is natural in the original exact zero-preserving functor. -/
def rowsInterchange (m n : SimplexCategory) : rows n ⋙ rows m ≅ rows m ⋙ rows n :=
  NatIso.ofComponents (fun W ↦ rowSwap W m n) (by
    intro V W F
    apply Model.Hom.ext
    apply CategoryTheory.Functor.ext (fun _ ↦ rfl))

/-- Move a fixed original row direction through the whole genuine simplicial row diagram. -/
def rowDiagramInterchange (W : Model.{u}) (n : SimplexCategory) :
    rowDiagram ((rows n).obj W) ≅ rowDiagram W ⋙ rows n :=
  NatIso.ofComponents (fun m ↦ rowSwap W m.unop n) (by
    intro m m' α
    apply Model.Hom.ext
    exact QuotientRows.transposeRows_reindex_outer W.waldhausen α.unop)

set_option maxHeartbeats 800000 in
-- The row-transpose equality exhausts the default 200000 heartbeats at `whnf`.
/-- At the original one-step row, transposition retains the full actual row. -/
lemma oneEmbedding_rowSwap (W : Model.{u}) (m : SimplexCategory) :
    QuotientRows.postcompose W.waldhausen (QuotientRows.waldhausenStructure W.waldhausen ⦋1⦌)
      (QuotientRows.oneEmbedding_exact W.waldhausen) m ⋙
      QuotientRows.transposeRows W.waldhausen m ⦋1⦌ =
        QuotientRows.oneEmbedding (QuotientRows.waldhausenStructure W.waldhausen m) := by
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro A
    apply ObjectProperty.FullSubcategory.ext
    refine CategoryTheory.Functor.ext ?_ ?_
    · rintro ⟨⟨i,j⟩,hij⟩
      fin_cases i <;> fin_cases j <;> rfl
    · rintro ⟨⟨i,j⟩,hij⟩ ⟨⟨k,l⟩,hkl⟩ f
      change i.val ≤ j.val at hij
      change k.val ≤ l.val at hkl
      fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l
      all_goals first
        | exact (QuotientRows.isZero W.waldhausen m).eq_of_src _ _
        | exact (QuotientRows.isZero W.waldhausen m).eq_of_tgt _ _
        | omega
        | simp only [QuotientRows.oneEmbedding, QuotientRows.postcompose,
            QuotientRows.oneDiagram, QuotientRows.oneIndex, QuotientRows.oneChain,
            ComposableArrows.mk₂, QuotientRows.transposeRows, QuotientRows.transposeDiagram,
            Functor.comp_obj, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.mk_one,
            eqToHom_refl, Category.comp_id, Category.id_comp]
      all_goals apply ObjectProperty.hom_ext; ext q; rfl
  · intro A B f
    apply ObjectProperty.hom_ext
    ext p q
    rcases p with ⟨⟨i,j⟩,hij⟩
    fin_cases i <;> fin_cases j
    all_goals first
      | exact W.waldhausen.isZero.eq_of_src _ _
      | exact W.waldhausen.isZero.eq_of_tgt _ _
      | simp [QuotientRows.oneEmbedding, QuotientRows.postcompose, QuotientRows.oneDiagram,
          QuotientRows.oneIndex, QuotientRows.oneChain, ComposableArrows.mk₂,
          ObjectProperty.FullSubcategory.comp_hom, QuotientRows.transposeRows]

/-- The new direction's one-row insertion is unchanged after the actual coordinate swap. -/
lemma insertion_rowSwap (W : Model.{u}) (m : SimplexCategory) {n : SimplexCategory}
    (τ : n ⟶ ⦋1⦌) :
    (rows m).map ((insertion τ).app W) ≫ (rowSwap W m n).hom =
      (insertion τ).app ((rows m).obj W) := by
  apply Model.Hom.ext
  change QuotientRows.postcompose W.waldhausen (QuotientRows.waldhausenStructure W.waldhausen n)
    ((QuotientRows.oneEmbedding_exact W.waldhausen).comp
      (QuotientRows.reindex_exact W.waldhausen τ)) m ⋙
    QuotientRows.transposeRows W.waldhausen m n =
    QuotientRows.oneEmbedding (QuotientRows.waldhausenStructure W.waldhausen m) ⋙
      QuotientRows.reindex (QuotientRows.waldhausenStructure W.waldhausen m) τ
  rw [← QuotientRows.postcompose_comp_postcompose W.waldhausen _
    (QuotientRows.oneEmbedding_exact W.waldhausen)
    _ (QuotientRows.reindex_exact W.waldhausen τ) m]
  rw [CategoryTheory.Functor.assoc, QuotientRows.transposeRows_reindex_inner,
    ← CategoryTheory.Functor.assoc, oneEmbedding_rowSwap]


end Quillen.Waldhausen.IteratedS
