/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.ExactCategory.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Natural pointwise short complexes

Actual zero composites give pointwise short complexes and full-subcategory lifts. Original additive mapping and whiskering preserve their exact original maps and the stated short exactness.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace Quillen.PerfectComplexes.ProjectiveLine.FlasqueDiagonal
/-- Termwise mapping retains an actual zero composite of natural transformations. -/
lemma mapComplexNatTrans_zero {A B : Type*} [Category A] [Category B]
    [Preadditive A] [Preadditive B] {F G H : A ⥤ B}
    [F.Additive] [G.Additive] [H.Additive] (a : F ⟶ G) (b : G ⟶ H) (h : a ≫ b = 0) :
    NatTrans.mapHomologicalComplex a (.up ℤ) ≫
      NatTrans.mapHomologicalComplex b (.up ℤ) = 0 := by
  rw [← NatTrans.mapHomologicalComplex_comp, h]
  apply NatTrans.ext
  funext K
  ext n : 1
  rfl

/-- Whiskering by an actual additive functor retains an actual zero composite. -/
lemma whiskeredNatTrans_zero {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Preadditive C] [Preadditive D] (I : A ⥤ B) {F G H : B ⥤ C}
    (a : F ⟶ G) (b : G ⟶ H) (h : a ≫ b = 0) (T : C ⥤ D) [T.Additive] :
    Functor.whiskerLeft I (Functor.whiskerRight a T) ≫
      Functor.whiskerLeft I (Functor.whiskerRight b T) = 0 := by
  apply NatTrans.ext
  funext K
  change T.map (a.app (I.obj K)) ≫ T.map (b.app (I.obj K)) = 0
  have hz : a.app (I.obj K) ≫ b.app (I.obj K) = 0 := NatTrans.congr_app h (I.obj K)
  rw [← T.map_comp, hz, T.map_zero]

/-- Two actual natural maps with zero composite retain their actual pointwise short complexes. -/
def naturalSequence {A B : Type*} [Category A] [Category B] [Preadditive B]
    {F G H : A ⥤ B} (a : F ⟶ G) (b : G ⟶ H) (h : a ≫ b = 0) :
    A ⥤ ShortComplex B where
  obj K := ShortComplex.mk (a.app K) (b.app K) (NatTrans.congr_app h K)
  map f := ShortComplex.homMk (F.map f) (G.map f) (H.map f) (a.naturality f) (b.naturality f)
  map_id K := by
    apply ShortComplex.hom_ext
    · exact F.map_id K
    · exact G.map_id K
    · exact H.map_id K
  map_comp f g := by
    apply ShortComplex.hom_ext
    · exact F.map_comp f g
    · exact G.map_comp f g
    · exact H.map_comp f g

/-- Source restriction retains a pointwise zero composite. -/
lemma whiskerLeftNatTrans_zero {A B C : Type*} [Category A] [Category B] [Category C]
    [Preadditive C] (I : A ⥤ B) {F G H : B ⥤ C}
    (a : F ⟶ G) (b : G ⟶ H) (h : a ≫ b = 0) :
    Functor.whiskerLeft I a ≫ Functor.whiskerLeft I b = 0 := by
  apply NatTrans.ext
  funext K
  exact NatTrans.congr_app h (I.obj K)

/-- The mapped sequence equation is checked abstractly before expanding the actual total. -/
lemma naturalSequence_whiskered_map {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D] [Preadditive C] [Preadditive D]
    (I : A ⥤ B) {F G H : B ⥤ C} (a : F ⟶ G) (b : G ⟶ H)
    (T : C ⥤ D) [T.Additive]
    (h₁ : Functor.whiskerLeft I a ≫ Functor.whiskerLeft I b = 0)
    (h₂ : Functor.whiskerLeft I (Functor.whiskerRight a T) ≫
      Functor.whiskerLeft I (Functor.whiskerRight b T) = 0) (K : A) :
    (naturalSequence (Functor.whiskerLeft I (Functor.whiskerRight a T))
      (Functor.whiskerLeft I (Functor.whiskerRight b T)) h₂).obj K =
      (((naturalSequence (Functor.whiskerLeft I a) (Functor.whiskerLeft I b) h₁).obj K).map
        T) := rfl

/-- Exactness transfers to the same literal whiskered maps before expanding the actual total. -/
lemma naturalSequence_whiskered_shortExact {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D] [Abelian C] [Abelian D]
    (I : A ⥤ B) {F G H : B ⥤ C} (a : F ⟶ G) (b : G ⟶ H)
    (T : C ⥤ D) [T.Additive]
    (h₁ : Functor.whiskerLeft I a ≫ Functor.whiskerLeft I b = 0)
    (h₂ : Functor.whiskerLeft I (Functor.whiskerRight a T) ≫
      Functor.whiskerLeft I (Functor.whiskerRight b T) = 0) (K : A)
    (hS : (((naturalSequence (Functor.whiskerLeft I a)
      (Functor.whiskerLeft I b) h₁).obj K).map T).ShortExact) :
    ((naturalSequence (Functor.whiskerLeft I (Functor.whiskerRight a T))
      (Functor.whiskerLeft I (Functor.whiskerRight b T)) h₂).obj K).ShortExact := by
  rw [naturalSequence_whiskered_map]
  exact hS

theorem naturalSequence_whiskered_shortExact_named_sequences
    {A B C D E : Type*} [Category A] [Category B] [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    (I : A ⥤ B) {F G H : B ⥤ C} (a : F ⟶ G) (b : G ⟶ H)
    (T : C ⥤ D) (P : D ⥤ E) [T.Additive] [P.Additive]
    (h₁ : Functor.whiskerLeft I a ≫ Functor.whiskerLeft I b = 0)
    (a' : I ⋙ F ⋙ (T ⋙ P) ⟶ I ⋙ G ⋙ (T ⋙ P))
    (b' : I ⋙ G ⋙ (T ⋙ P) ⟶ I ⋙ H ⋙ (T ⋙ P))
    (h₂ : a' ≫ b' = 0)
    (ha : a' = Functor.whiskerLeft I (Functor.whiskerRight a (T ⋙ P)))
    (hb : b' = Functor.whiskerLeft I (Functor.whiskerRight b (T ⋙ P))) (K : A)
    (S : ShortComplex C) (U : ShortComplex E)
    (hSdef : S = (naturalSequence (Functor.whiskerLeft I a)
      (Functor.whiskerLeft I b) h₁).obj K)
    (hUdef : U = (naturalSequence a' b' h₂).obj K)
    (hS : ((S.map T).map P).ShortExact) : U.ShortExact := by
  subst a'
  subst b'
  subst S
  subst U
  apply naturalSequence_whiskered_shortExact I a b (T ⋙ P) h₁ h₂ K
  simpa only [ShortComplex.map_comp] using hS

/-- Lift a literal sequence using the supplied membership proofs without changing any maps. -/
def liftedSequence {A B : Type*} [Category A] [Category B] [Preadditive B]
    (P : ObjectProperty B) {F G H : A ⥤ B}
    (hF : ∀ K, P (F.obj K)) (hG : ∀ K, P (G.obj K)) (hH : ∀ K, P (H.obj K))
    (a : F ⟶ G) (b : G ⟶ H) (h : a ≫ b = 0) (K : A) :
    ShortComplex P.FullSubcategory :=
  { X₁ := (P.lift F hF).obj K
    X₂ := (P.lift G hG).obj K
    X₃ := (P.lift H hH).obj K
    f := ObjectProperty.homMk (a.app K)
    g := ObjectProperty.homMk (b.app K)
    zero := ObjectProperty.hom_ext _ (NatTrans.congr_app h K) }

/-- Forgetting a lifted literal sequence recovers the entire original sequence. -/
lemma liftedSequence_underlying {A B : Type*} [Category A] [Category B] [Preadditive B]
    (P : ObjectProperty B) {F G H : A ⥤ B}
    (hF : ∀ K, P (F.obj K)) (hG : ∀ K, P (G.obj K)) (hH : ∀ K, P (H.obj K))
    (a : F ⟶ G) (b : G ⟶ H) (h : a ≫ b = 0) (K : A) :
    (liftedSequence P hF hG hH a b h K).map P.ι = (naturalSequence a b h).obj K := rfl


end Quillen.PerfectComplexes.ProjectiveLine.FlasqueDiagonal
end
end
