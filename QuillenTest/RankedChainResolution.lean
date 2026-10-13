/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.CategoryTheory.RankedChain.Resolution

/-! # Semantic consumers of actual ranked-chain poset resolution -/
@[expose] public section

noncomputable section
open CategoryTheory
open Quillen.RankedChainOrder
universe u
namespace QuillenTest.RankedChainResolution

open Quillen
variable {C : Type u} [SmallCategory C] (rank : C → ℕ)

/-- Equal-rank original arrows really are identities up to literal object
equality, by the directness condition rather than an extra compression axiom. -/
theorem equal_rank_compresses (h : IsDirectRank C rank) {X Y : C} (f : X ⟶ Y)
    (he : rank X = rank Y) : ∃ e : X = Y, f = eqToHom e := by
  exact (h f).resolve_left (by rw [he]; exact lt_irrefl _)

/-- Terminal-identity compression retains the complete old comma object. -/
theorem closed_object_unchanged {Y : C} (S : CostructuredArrow (lastVertex C rank) Y)
    (hS : IsClosed C rank S) : closeObj C rank S = S := by
  obtain ⟨e, _⟩ := hS
  have hn : ¬rank ((lastVertex C rank).obj S.left) < rank Y := by
    rw [e]
    exact lt_irrefl _
  simp only [closeObj, dite_eq_right hn]

/-- The mixed case retains a real map into the unextended closed target. -/
theorem mixed_append_to_unchanged {Y : C}
    (S B : CostructuredArrow (lastVertex C rank) Y)
    (hS : rank ((lastVertex C rank).obj S.left) < rank Y)
    (hB : IsClosed C rank B) (f : S ⟶ B) :
    Nonempty (appendCommaObj C rank S hS ⟶ B) ∧ closeObj C rank B = B :=
  ⟨exists_appendComma_to_closed C rank S B hS hB f, closed_object_unchanged rank B hB⟩

/-- The appended source has the exact original final arrow, not just the
same endpoint objects. -/
theorem prescribed_append_composite (A : Obj C rank) {Y : C}
    (q : A.chain.obj (Fin.last A.dim) ⟶ Y)
    (hq : rank (A.chain.obj (Fin.last A.dim)) < rank Y) :
    (lastVertex C rank).map (homOfFace C rank (appendFace C rank A q hq)) ≫
      eqToHom (ComposableArrows.appendChain_obj_last A.chain q) = q :=
  appendFace_lastMap C rank A q hq

/-- A genuine one-arrow strict chain, retaining the specified original arrow. -/
def edgeChain {X Y : C} (f : X ⟶ Y) (h : rank X < rank Y) : Obj C rank where
  dim := 1
  chain := CategoryTheory.ComposableArrows.mk₁ f
  strict := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact h

/-- Parallel original arrows with the same vertices remain distinct actual
chains and have no face relation identifying their full arrow data. -/
theorem distinct_parallel_edges {X Y : C} (f g : X ⟶ Y) (h : rank X < rank Y)
    (hne : f ≠ g) :
    edgeChain rank f h ≠ edgeChain rank g h ∧
      ¬Nonempty (Face C rank (edgeChain rank f h) (edgeChain rank g h)) := by
  have hn : ¬Nonempty (Face C rank (edgeChain rank f h) (edgeChain rank g h)) := by
    rintro ⟨a⟩
    have ha := a.face
    rw [self_embedding_eq_refl a.index] at ha
    change CategoryTheory.ComposableArrows.mk₁ g = CategoryTheory.ComposableArrows.mk₁ f at ha
    have he := CategoryTheory.Functor.congr_hom ha (homOfLE (show (0 : Fin 2) ≤ 1 from by decide))
    have hgf : g = f := by simpa using he
    exact hne hgf.symm
  refine ⟨?_, hn⟩
  intro he
  apply hn
  rw [he]
  exact ⟨Face.id C rank _⟩

/-- Both sides of the actual contraction meet in the same closure functor. -/
theorem genuine_comma_contraction (h : IsDirectRank C rank) (Y : C) :
    Nonempty (𝟭 (CostructuredArrow (lastVertex C rank) Y) ⟶ closeFunctor C rank h Y) ∧
      Nonempty ((Functor.const (CostructuredArrow (lastVertex C rank) Y)).obj
        (vertexComma C rank Y) ⟶ closeFunctor C rank h Y) ∧
      ContractibleSpace (ClassifyingSpace (CostructuredArrow (lastVertex C rank) Y)) :=
  ⟨⟨identityToClose C rank h Y⟩, ⟨constantToClose C rank h Y⟩, comma_contractible C rank h Y⟩

/-- The resolution retains the literal original terminal vertex twice. -/
theorem original_vertex (A : ResolutionPoset C) :
    (resolutionFunctor C).obj A =
      (A.chain.obj (Fin.last A.dim)).chain.obj
        (Fin.last (A.chain.obj (Fin.last A.dim)).dim) := rfl

/-- The actual homotopy equivalence's forward map is the original displayed
poset-resolution functor, ready for exact compact-domain factorization. -/
theorem original_resolution_map :
    (resolutionHomotopyEquiv C).toFun = (classifyingSpaceMap (resolutionFunctor C)).hom :=
  resolutionHomotopyEquiv_toFun C

/-- The construction does not manufacture vertices when the original category
is empty. -/
theorem empty_resolution [IsEmpty C] : IsEmpty (ResolutionPoset C) :=
  ⟨fun A ↦ isEmptyElim ((resolutionFunctor C).obj A)⟩

end QuillenTest.RankedChainResolution
