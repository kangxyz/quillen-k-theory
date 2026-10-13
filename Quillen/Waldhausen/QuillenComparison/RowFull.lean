/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.QuillenComparison.SparseRows

/-! # Fullness of the exact-row Q comparison -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe v u

namespace Quillen.Waldhausen.QuillenComparison

/-- The endpoints of central nested intervals cover every vertex of the
edgewise indexing ordinal. -/
theorem centralEndpointsCover (n : SimplexCategory) (k : Fin ((Edgewise.ε.obj n).len + 1)) :
    (∃ i, (centralInterval n i).left = k) ∨ ∃ i, (centralInterval n i).right = k := by
  rcases Edgewise.join_cases k with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact Or.inl ⟨i.rev, by simp [centralInterval, NestedInterval.left, lowerIndex]⟩
  · exact Or.inr ⟨i, rfl⟩

/-- The whole ordinal, viewed as its maximal containment interval. -/
def topNested (n : SimplexCategory) : NestedInterval n :=
  ⟨(OrderDual.toDual 0, Fin.last n.len), Fin.zero_le _⟩

/-- The canonical simplification rule for the underlying construction. -/
@[simp] theorem nestedToInterval_topNested_edgewise (n : SimplexCategory) :
    nestedToInterval (topNested (Edgewise.ε.obj n)) =
      interval 0 (Fin.last (Edgewise.ε.obj n).len) (Fin.zero_le _) := rfl


@[simp]
theorem centralInterval_last (n : SimplexCategory) :
    centralInterval n (Fin.last n.len) = topNested (Edgewise.ε.obj n) :=
  Subtype.ext (Prod.ext (lowerIndex_last n) (upperIndex_last n))

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : Quillen.ExactStructure C)

/-- Normalizing a terminal interval transports the original Q-span to the
literal whole-row span, with exactly the induced endpoint isomorphism. -/
theorem intervalSpan_to_whole {n : SimplexCategory} (F : Row E n)
    (p q : NestedInterval n) (h : p ≤ q) (hq : q = topNested n) :
    Q.mkHom E.deflation E.inflation (intervalSpan E F.simplex 0 h) ≫
      (E.qIsoOfIso (eqToIso (congrArg (fun p ↦ F.diagram.obj (nestedToInterval p)) hq))).hom =
      Q.mkHom E.deflation E.inflation (wholeSpan E F p) := by
  subst q
  change Q.mkHom E.deflation E.inflation (intervalSpan E F.simplex 0 h) ≫ 𝟙 _ = _
  rw [Category.comp_id]
  rfl

/-- The natural target identification on the final central quotient. -/
def centralTopIso {n : SimplexCategory} (F : Row E (Edgewise.ε.obj n)) :
    F.diagram.obj (nestedToInterval (centralInterval n (Fin.last n.len))) ≅
      (initialFlag E F).obj (Fin.last (Edgewise.ε.obj n).len) :=
  eqToIso (congrArg (fun p ↦ F.diagram.obj (nestedToInterval p)) (centralInterval_last n))

/-- A terminal Q-chain arrow is exactly its whole-row span after the explicit
target identification. -/
theorem rowChain_arrow_to_whole {n : SimplexCategory} (F : Row E (Edgewise.ε.obj n))
    (i : Fin (n.len + 1)) :
    ((rowChainComparison E n).obj F).of.map (homOfLE (Fin.le_last i)) ≫
      (E.qIsoOfIso (centralTopIso E F)).hom =
      Q.mkHom E.deflation E.inflation (wholeSpan E F (centralInterval n i)) :=
  intervalSpan_to_whole E F _ _ _ (centralInterval_last n)

/-- Q-naturality on central intervals is enough to lift all the prescribed
central components to a unique original row isomorphism. -/
theorem existsUnique_rowIso_of_central_spans {n : SimplexCategory}
    {F G : Row E (Edgewise.ε.obj n)}
    (a : ∀ i, F.diagram.obj (nestedToInterval (centralInterval n i)) ≅
      G.diagram.obj (nestedToInterval (centralInterval n i)))
    (b : (initialFlag E F).obj (Fin.last (Edgewise.ε.obj n).len) ≅
      (initialFlag E G).obj (Fin.last (Edgewise.ε.obj n).len))
    (h : ∀ i, Q.mkHom E.deflation E.inflation (wholeSpan E F (centralInterval n i)) ≫
        (E.qIsoOfIso b).hom = (E.qIsoOfIso (a i)).hom ≫
          Q.mkHom E.deflation E.inflation (wholeSpan E G (centralInterval n i))) :
    ∃! e : F ⟶ G, ∀ i, e.hom.app (nestedToInterval (centralInterval n i)) = (a i).hom := by
  obtain ⟨e, he⟩ := exists_rowIso_of_covering_spans E (centralInterval n)
    (centralEndpointsCover n) a b h
  refine ⟨e, he, ?_⟩
  intro f hf
  apply Iso.ext
  apply rowNatTrans_ext_top E
  have hh := (hf (Fin.last n.len)).trans (he (Fin.last n.len)).symm
  rw [centralInterval_last, nestedToInterval_topNested_edgewise] at hh
  exact hh

/-- Every natural isomorphism of the compared Q-chains lifts to an actual
isomorphism of exact quotient rows. -/
instance rowChainComparison_full (n : SimplexCategory) : (rowChainComparison E n).Full where
  map_surjective {F G} φ := by
    have hh (i : Fin (n.len + 1)) :
        ∃ a : F.diagram.obj (nestedToInterval (centralInterval n i)) ≅
          G.diagram.obj (nestedToInterval (centralInterval n i)), E.qIsoOfIso a = φ.iso.app i :=
      E.qIsoOfIso_bijective.surjective (φ.iso.app i)
    choose a ha using hh
    let b := (centralTopIso E F).symm ≪≫ a (Fin.last n.len) ≪≫ centralTopIso E G
    have hb : (E.qIsoOfIso (centralTopIso E F)).hom ≫ (E.qIsoOfIso b).hom =
        (E.qIsoOfIso (a (Fin.last n.len))).hom ≫ (E.qIsoOfIso (centralTopIso E G)).hom := by
      rw [← Iso.trans_hom, ← ExactStructure.qIsoOfIso_trans,
        ← Iso.trans_hom, ← ExactStructure.qIsoOfIso_trans]
      congr 2
      simp [b]
    have h (i : Fin (n.len + 1)) :
        Q.mkHom E.deflation E.inflation (wholeSpan E F (centralInterval n i)) ≫
          (E.qIsoOfIso b).hom = (E.qIsoOfIso (a i)).hom ≫
            Q.mkHom E.deflation E.inflation (wholeSpan E G (centralInterval n i)) := by
      rw [← rowChain_arrow_to_whole E F i, ← rowChain_arrow_to_whole E G i,
        Category.assoc, hb]
      have hai := congrArg Iso.hom (ha i)
      have hal := congrArg Iso.hom (ha (Fin.last n.len))
      change (E.qIsoOfIso (a i)).hom = φ.iso.hom.app i at hai
      change (E.qIsoOfIso (a (Fin.last n.len))).hom = φ.iso.hom.app (Fin.last n.len) at hal
      rw [hai, hal, φ.iso.hom.naturality_assoc]
    obtain ⟨e, he, _⟩ := existsUnique_rowIso_of_central_spans E a b h
    refine ⟨e, ?_⟩
    apply Core.hom_ext
    ext i
    change (E.qIsoOfIso (e.app (nestedToInterval (centralInterval n i)))).hom = φ.iso.hom.app i
    rw [show e.app (nestedToInterval (centralInterval n i)) = a i from Iso.ext (he i)]
    exact congrArg Iso.hom (ha i)

end Quillen.Waldhausen.QuillenComparison
