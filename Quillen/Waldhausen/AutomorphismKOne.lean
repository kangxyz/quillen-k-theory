/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyGroups.Loop.KOneNormalization
public import Quillen.Waldhausen.GrothendieckComparison.WeakObjectCompositionTrack
public import Quillen.Waldhausen.GrothendieckComparison.ObjectNaturality

/-! Original weak-endomorphism and automorphism classes in homotopical K-one. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite Convexity
open scoped Simplicial Topology
universe u v

namespace Quillen.Waldhausen.Structure
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- The original weak-arrow loop, normalized from its actual object component into K-one. -/
def weakEndomorphismKOneClass {A : C} (f : A ⟶ A) (hf : W.weq f) : W.K 1 :=
  loopKOneNormalization (W.kZeroObjectLoop A) ⟦W.weakObjectSquareLoopPath f hf⟧

/-- Equality of original endomorphisms gives equality of their normalized classes. -/
theorem weakEndomorphismKOneClass_congr {A : C} {f g : A ⟶ A}
    (h : f = g) (hf : W.weq f) (hg : W.weq g) :
    W.weakEndomorphismKOneClass f hf = W.weakEndomorphismKOneClass g hg := by
  subst g
  rfl

/-- An actual automorphism supplies its own original fine weak-arrow K-one class. -/
def automorphismKOneClass {A : C} (e : A ≅ A) : W.K 1 :=
  W.weakEndomorphismKOneClass e.hom (W.weq_iso e.hom inferInstance)

/-- The identity weak-arrow loop is the literal constant path at the object loop. -/
theorem weakObjectSquareLoopPath_id (A : C) :
    W.weakObjectSquareLoopPath (𝟙 A) (W.weq.id_mem A) = Path.refl (W.kZeroObjectLoop A) := by
  apply Path.ext
  funext s
  apply Path.ext
  funext t
  exact W.weakObjectIdentitySquare_realization A s t

/-- The identity automorphism represents the identity element of the original K-one group. -/
theorem automorphismKOneClass_refl (A : C) : W.automorphismKOneClass (Iso.refl A) = 1 := by
  change loopKOneNormalization (W.kZeroObjectLoop A)
    (⟦W.weakObjectSquareLoopPath (𝟙 A) (W.weq.id_mem A)⟧ :
      FundamentalGroup _ (W.kZeroObjectLoop A)) = 1
  rw [weakObjectSquareLoopPath_id]
  exact (loopKOneNormalization (W.kZeroObjectLoop A)).map_one

/-- Composition follows the original weak-arrow triangle and the fundamental-group convention. -/
theorem weakEndomorphismKOneClass_comp {A : C} (f g : A ⟶ A)
    (hf : W.weq f) (hg : W.weq g) :
    W.weakEndomorphismKOneClass (f ≫ g) (W.weq.comp_mem _ _ hf hg) =
      W.weakEndomorphismKOneClass g hg * W.weakEndomorphismKOneClass f hf := by
  have he : (⟦W.weakObjectSquareLoopPath (f ≫ g) (W.weq.comp_mem _ _ hf hg)⟧ :
      FundamentalGroup _ (W.kZeroObjectLoop A)) =
      ⟦(W.weakObjectSquareLoopPath f hf).trans (W.weakObjectSquareLoopPath g hg)⟧ :=
    Quotient.sound ⟨(W.weakObjectSquareCompositionTrack f g hf hg).symm⟩
  let a : FundamentalGroup (Path W.kBasepoint W.kBasepoint) (W.kZeroObjectLoop A) :=
    ⟦W.weakObjectSquareLoopPath f hf⟧
  let b : FundamentalGroup (Path W.kBasepoint W.kBasepoint) (W.kZeroObjectLoop A) :=
    ⟦W.weakObjectSquareLoopPath g hg⟧
  have hab : b * a =
      ⟦(W.weakObjectSquareLoopPath f hf).trans (W.weakObjectSquareLoopPath g hg)⟧ := rfl
  change loopKOneNormalization (W.kZeroObjectLoop A) _ =
    loopKOneNormalization (W.kZeroObjectLoop A) b * loopKOneNormalization (W.kZeroObjectLoop A) a
  rw [he, ← hab]
  exact (loopKOneNormalization (W.kZeroObjectLoop A)).map_mul b a

/-- Actual automorphisms act by their original weak-arrow classes in K-one. -/
def automorphismKOneHom (A : C) : Aut A →* W.K 1 where
  toFun := W.automorphismKOneClass
  map_one' := W.automorphismKOneClass_refl A
  map_mul' e f := W.weakEndomorphismKOneClass_comp f.hom e.hom
    (W.weq_iso _ inferInstance) (W.weq_iso _ inferInstance)

/-- The original square path respects equality of its arrow, independently of its certificate. -/
theorem weakObjectSquareLoopPath_congr {A B : C} {f g : A ⟶ B}
    (h : f = g) (hf : W.weq f) (hg : W.weq g) :
    W.weakObjectSquareLoopPath f hf = W.weakObjectSquareLoopPath g hg := by
  subst g
  rfl

/-- The original class is invariant under a specified weak-arrow intertwining isomorphism. -/
theorem weakEndomorphismKOneClass_iso {A B : C} (e : A ≅ B)
    (f : A ⟶ A) (g : B ⟶ B) (hf : W.weq f) (hg : W.weq g)
    (h : f ≫ e.hom = e.hom ≫ g) :
    W.weakEndomorphismKOneClass f hf = W.weakEndomorphismKOneClass g hg := by
  let he := W.weq_iso e.hom inferInstance
  let p := W.weakObjectSquareLoopPath e.hom he
  let α := W.weakObjectSquareLoopPath f hf
  let β := W.weakObjectSquareLoopPath g hg
  have H : (α.trans p).Homotopy (p.trans β) :=
    (W.weakObjectSquareCompositionTrack f e.hom hf he).trans
      (((W.weakObjectSquareCompositionTrack e.hom g he hg).symm).cast
        (W.weakObjectSquareLoopPath_congr h.symm _ _) rfl)
  let ca : FundamentalGroupoid (Path W.kBasepoint W.kBasepoint) :=
    FundamentalGroupoid.mk (W.kZeroObjectLoop A)
  let cb : FundamentalGroupoid (Path W.kBasepoint W.kBasepoint) :=
    FundamentalGroupoid.mk (W.kZeroObjectLoop B)
  let c : ca ⟶ cb := ⟦p⟧
  let aa : ca ⟶ ca := ⟦α⟧
  let bb : cb ⟶ cb := ⟦β⟧
  have ht : aa ≫ c = c ≫ bb := by
    change (⟦α.trans p⟧ : Path.Homotopic.Quotient _ _) = ⟦p.trans β⟧
    exact Quotient.sound ⟨H⟩
  have hp : FundamentalGroup.fundamentalGroupMulEquivOfPath p ⟦α⟧ = ⟦β⟧ := by
    change Groupoid.inv c ≫ aa ≫ c = bb
    rw [ht]
    simp
  change loopKOneNormalization (W.kZeroObjectLoop A) ⟦α⟧ =
    loopKOneNormalization (W.kZeroObjectLoop B) ⟦β⟧
  rw [← loopKOneNormalization_transport p, hp]

end Quillen.Waldhausen.Structure

namespace Quillen.Waldhausen
open QuotientRows
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {V : Structure C} {W : Structure D} {F : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)

/-- Exact functors preserve the actual entire bisimplex family by postcomposition. -/
theorem bisimplexFamily_postcompose {n m : ℕ}
    (G : Grid₂ ⦋n⦌ ⦋m⦌ ⥤ C) (hG : IsSimplex₂ V.cof V.weq G) :
    bisimplexFamily V G hG ≫ sSetMap hF =
      bisimplexFamily W (G ⋙ F) (hG.postcomp V.cof V.weq hF) := by
  ext k z
  apply Subtype.ext
  rfl

/-- Both independent simplex coordinates are retained by the original exact realization map. -/
theorem bisimplexRealization_postcompose {n m : ℕ}
    (G : Grid₂ ⦋n⦌ ⦋m⦌ ⥤ C) (hG : IsSimplex₂ V.cof V.weq G)
    (z : StdSimplex ℝ (Fin (n + 1))) (t : StdSimplex ℝ (Fin (m + 1))) :
    deloopingMap hF (bisimplexRealization V G hG (z, t)) =
      bisimplexRealization W (G ⋙ F) (hG.postcomp V.cof V.weq hF) (z, t) := by
  change (SSet.toTop.map (bisimplexFamily V G hG) ≫
    SSet.toTop.map (sSetMap hF)) ((realizationProductSimplexHomeomorph n m).symm (z, t)) = _
  rw [← Functor.map_comp, bisimplexFamily_postcompose]
  rfl

/-- A strictly zero-preserving exact functor keeps every cell of the original weak-arrow square. -/
theorem weakObjectSimplex_postcompose (h0 : F.obj V.zero = W.zero)
    {A B : C} (f : A ⟶ B) (hf : V.weq f) :
    (V.weakObjectSimplex f hf).val ⋙ F =
      (W.weakObjectSimplex (F.map f) (hF.weak f hf)).val := by
  refine CategoryTheory.Functor.ext ?_ ?_
  · rintro ⟨s, ⟨⟨i, j⟩, hij⟩⟩
    fin_cases s <;> fin_cases i <;> fin_cases j
    all_goals first
      | exact h0
      | rfl
  · rintro ⟨s, ⟨⟨i, j⟩, hij⟩⟩ ⟨t, ⟨⟨k, l⟩, hkl⟩⟩ a
    have hst := (leOfHom a).1
    change s.val ≤ t.val at hst
    change i.val ≤ j.val at hij
    change k.val ≤ l.val at hkl
    fin_cases s <;> fin_cases t <;> fin_cases i <;> fin_cases j <;>
      fin_cases k <;> fin_cases l
    all_goals try { simp at hst }
    all_goals try { simp at hij }
    all_goals try { simp at hkl }
    all_goals first
      | omega
      | exact (hF.zero V.isZero).eq_of_src _ _
      | exact (hF.zero V.isZero).eq_of_tgt _ _
      | simp [Structure.weakObjectSimplex, weakChainToGrid, Structure.oneWeakArrow,
          oneEmbedding, oneDiagram, oneIndex, oneChain, ComposableArrows.mk₁,
          ComposableArrows.mk₂]

/-- The based realization carries the actual object loop to its original image object loop. -/
theorem objectLoopMapEq (h0 : F.obj V.zero = W.zero) (A : C) :
    basedLoopMap (deloopingMap hF).hom (deloopingMap_basepoint_of_zeroEq hF h0)
        (V.kZeroObjectLoop A) = W.kZeroObjectLoop (F.obj A) :=
  deloopingMap_kZeroObjectLoop hF h0 A

/-- The full original weak-arrow path retains both coordinates under exact postcomposition. -/
theorem weakObjectSquareLoopPath_postcompose (h0 : F.obj V.zero = W.zero)
    {A : C} (f : A ⟶ A) (hf : V.weq f) :
    ((V.weakObjectSquareLoopPath f hf).map
      (basedLoopMap (deloopingMap hF).hom
        (deloopingMap_basepoint_of_zeroEq hF h0)).continuous).cast
        (objectLoopMapEq hF h0 A).symm (objectLoopMapEq hF h0 A).symm =
      W.weakObjectSquareLoopPath (F.map f) (hF.weak f hf) := by
  apply Path.ext
  funext s
  apply Path.ext
  funext t
  change deloopingMap hF
      (bisimplexRealization V (V.weakObjectSimplex f hf).val
        ((isSimplex₂_diagonal_iff _ _ _).mpr (V.weakObjectSimplex f hf).property)
        (StdSimplex.homeomorphI.symm t, StdSimplex.homeomorphI.symm s)) = _
  rw [bisimplexRealization_postcompose]
  exact DFunLike.congr_fun (bisimplexRealization_congr W _ _
    ((isSimplex₂_diagonal_iff _ _ _).mpr
      (W.weakObjectSimplex (F.map f) (hF.weak f hf)).property)
    (weakObjectSimplex_postcompose hF h0 f hf))
    (StdSimplex.homeomorphI.symm t, StdSimplex.homeomorphI.symm s)

/-- A strict zero equality gives naturality through the original unmodified realization map. -/
theorem KMap_weakEndomorphismKOneClass_of_zeroEq (h0 : F.obj V.zero = W.zero)
    {A : C} (f : A ⟶ A) (hf : V.weq f) :
    KMap hF 1 (V.weakEndomorphismKOneClass f hf) =
      W.weakEndomorphismKOneClass (F.map f) (hF.weak f hf) := by
  rw [KMap_eq_piMap_of_zeroEq hF h0 1]
  unfold Structure.weakEndomorphismKOneClass
  rw [loopKOneNormalization_naturality_of_loopEq (deloopingMap hF).hom
    (deloopingMap_basepoint_of_zeroEq hF h0) (V.kZeroObjectLoop A)
    (W.kZeroObjectLoop (F.obj A)) (objectLoopMapEq hF h0 A)]
  rw [weakObjectSquareLoopPath_postcompose hF h0 f hf]

/-- Every original K-map preserves the independently defined weak-endomorphism class.
The proof retains its canonical chosen-zero rebase and the actual object isomorphism. -/
theorem KMap_weakEndomorphismKOneClass {A : C} (f : A ⟶ A) (hf : V.weq f) :
    KMap hF 1 (V.weakEndomorphismKOneClass f hf) =
      W.weakEndomorphismKOneClass (F.map f) (hF.weak f hf) := by
  let e := rebaseFunctorIso F V.zero W.zero ((hF.zero V.isZero).iso W.isZero)
  have hn := KMap_weakEndomorphismKOneClass_of_zeroEq hF.rebase
    (rebaseFunctor_obj_base _ _ _ _) f hf
  rw [KMap_eq_piMap_of_zeroEq hF.rebase (rebaseFunctor_obj_base _ _ _ _) 1] at hn
  rw [KMap_eq_piMap]
  exact hn.trans (W.weakEndomorphismKOneClass_iso (e.app A) (F.map f) _
    (hF.weak f hf) (hF.rebase.weak f hf) (e.hom.naturality f)).symm

/-- The intrinsic automorphism class is natural for the original canonically based K-map. -/
theorem KMap_automorphismKOneClass {A : C} (e : A ≅ A) :
    KMap hF 1 (V.automorphismKOneClass e) = W.automorphismKOneClass (F.mapIso e) :=
  KMap_weakEndomorphismKOneClass hF e.hom (V.weq_iso _ inferInstance)

end Quillen.Waldhausen
