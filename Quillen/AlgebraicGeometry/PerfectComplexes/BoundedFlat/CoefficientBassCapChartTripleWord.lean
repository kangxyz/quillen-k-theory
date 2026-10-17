/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NativeReferenceWordCoherence
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TripleLeftColumnNodes

/-!
# The full normalized reference word of a cap chart join

Two actual geometric chart squares identify the postcomposed polynomial-cap anchor with
its fixed Laurent three-factor reference. The theorem retains every binary normalization,
equality transport, and whiskered chart-square factor; its small-model image is obtained
without changing any of those factors.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
universe u v
namespace Quillen.PerfectComplexes.CoefficientBassCapChartTripleWord
open BassReferenceMerge BassH0Merge

private theorem cancel_iso_middle {C₀ : Type*} [Category* C₀]
    {A B C D E : C₀} (i : A ≅ B) (j : B ≅ C) (k : A ≅ D) (l : D ≅ C)
    (m : D ≅ E) (h : i ≪≫ j = k ≪≫ l) :
    i ≪≫ j ≪≫ l.symm ≪≫ m = k ≪≫ m := by
  rw [← Iso.trans_assoc i j, h]
  simp only [Iso.trans_assoc, Iso.self_symm_id_assoc]

private theorem rearrange_square_word {C₀ : Type*} [Category* C₀]
    {A B C D E F : C₀} (a : A ≅ B) (b : B ≅ C) (t : C ≅ D)
    (d : A ≅ E) (e : E ≅ D) (k : B ≅ F)
    (sq : a ≪≫ b ≪≫ t = d ≪≫ e) :
    (e ≪≫ t.symm) ≪≫ (b.symm ≪≫ k) = d.symm ≪≫ a ≪≫ k := by
  have hs := congrArg
    (fun i ↦ d.symm ≪≫ i ≪≫ t.symm ≪≫ b.symm ≪≫ k) sq
  simpa only [Iso.trans_assoc, Iso.symm_self_id_assoc,
    Iso.self_symm_id_assoc] using hs.symm

private theorem small_symm {C₀ D₀ : Type u} [Category.{v} C₀] [Category.{v} D₀]
    {F G : C₀ ⥤ D₀} (e : F ≅ G) : (smallIso e).symm = smallIso e.symm := rfl

private abbrev smallFunctor {A B : Type u} [Category.{v} A] [Category.{v} B]
    (F : A ⥤ B) : AsSmall.{0} A ⥤ AsSmall.{0} B :=
  AsSmall.down ⋙ F ⋙ AsSmall.up

private abbrev smallComparison {A B : Type u} [Category.{v} A] [Category.{v} B]
    {F G : A ⥤ B} (e : F ≅ G) : smallFunctor F ≅ smallFunctor G := smallIso e

private theorem transport_model_word
    {X₀ Y₀ Z₀ U₀ V₀ W₀ : Type u}
    [Category.{v} X₀] [Category.{v} Y₀] [Category.{v} Z₀]
    [Category.{v} U₀] [Category.{v} V₀] [Category.{v} W₀]
    (L : Y₀ ⥤ X₀) (K : Z₀ ⥤ Y₀) (A : U₀ ⥤ Z₀) (J : V₀ ⥤ Y₀)
    (D : W₀ ⥤ X₀) (M : V₀ ⥤ W₀) (H : U₀ ⥤ V₀)
    {S T : V₀ ⥤ X₀} {P Q : U₀ ⥤ Y₀} {R : U₀ ⥤ W₀}
    {B : Z₀ ⥤ X₀} {F₀ F₁ : U₀ ⥤ X₀}
    (mh : R ≅ H ⋙ M) (lj : S ≅ J ⋙ L) (eq₂ : S ≅ T) (dm : T ≅ M ⋙ D)
    (jh : P ≅ H ⋙ J) (eq₁ : P ≅ Q) (ka : Q ≅ A ⋙ K)
    (dmh : F₀ ≅ R ⋙ D) (eqt : F₀ ≅ F₁) (lka : F₁ ≅ A ⋙ B) (lk : B ≅ K ⋙ L)
    (hw :
      (isoWhiskerRight mh D ≪≫
        (isoWhiskerLeft H (lj.symm ≪≫ eq₂ ≪≫ dm)).symm) ≪≫
        isoWhiskerRight (jh.symm ≪≫ eq₁ ≪≫ ka) L =
      dmh.symm ≪≫ eqt ≪≫ lka ≪≫ isoWhiskerLeft A lk) :
    ((isoWhiskerRight (smallComparison mh) (smallFunctor D) ≪≫
      (isoWhiskerLeft (smallFunctor H)
        ((smallComparison lj).symm ≪≫ smallComparison eq₂ ≪≫ smallComparison dm)).symm) ≪≫
      isoWhiskerRight ((smallComparison jh).symm ≪≫ smallComparison eq₁ ≪≫
        smallComparison ka) (smallFunctor L) :
      smallFunctor R ⋙ smallFunctor D ≅
        (smallFunctor A ⋙ smallFunctor K) ⋙ smallFunctor L) =
    (smallComparison dmh).symm ≪≫ smallComparison eqt ≪≫ smallComparison lka ≪≫
      isoWhiskerLeft (smallFunctor A) (smallComparison lk) := by
  apply Iso.ext
  apply NatTrans.ext
  funext x
  have hs := congrArg (fun e ↦
    (AsSmall.up : X₀ ⥤ AsSmall.{0} X₀).map
      (e.hom.app ((AsSmall.down : AsSmall.{0} U₀ ⥤ U₀).obj x))) hw
  simp only [smallComparison, smallFunctor, smallIso, Iso.trans_hom, Iso.symm_hom,
    Iso.symm_inv, Iso.trans_inv, isoWhiskerLeft_hom, isoWhiskerLeft_inv,
    isoWhiskerRight_hom, isoWhiskerRight_inv, NatTrans.comp_app, whiskerLeft_app,
    whiskerRight_app, Functor.comp_obj, Functor.comp_map, Functor.map_comp,
    Category.assoc] at hs ⊢
  simpa only [AsSmall.down_obj, AsSmall.up_obj_down, AsSmall.down_map,
    AsSmall.up_map_down] using hs

local notation "N" => boundedFlatNormalizedPullback
local notation "C" => boundedFlatNormalizedPullbackCompIso

private theorem split_square_word {A₀ B₀ A₁ B₁ X : Scheme.{u}}
    (l : B₁ ⟶ B₀) (ja : B₀ ⟶ A₀) (jb : B₁ ⟶ A₁) (m : A₁ ⟶ A₀)
    (h : A₀ ⟶ X) (sq : l ≫ ja = jb ≫ m) (tot : l ≫ ja ≫ h = jb ≫ m ≫ h) :
    C l (ja ≫ h) ≪≫ isoWhiskerRight (C ja h) (N l) ≪≫
      isoWhiskerLeft (N h) (C l ja).symm ≪≫
      isoWhiskerLeft (N h) (eqToIso (congrArg N sq) ≪≫ C jb m) =
    eqToIso (congrArg N tot) ≪≫ C jb (m ≫ h) ≪≫
      isoWhiskerRight (C m h) (N jb) := by
  have first := anchored_factorizations_strict l ja h (l ≫ ja) (ja ≫ h)
    (l ≫ ja ≫ h) rfl rfl (Category.assoc l ja h).symm rfl
  have second := anchored_factorizations_strict jb m h (l ≫ ja) (m ≫ h)
    (l ≫ ja ≫ h) sq rfl (Category.assoc l ja h).symm tot
  simp only [eqToIso_refl, Iso.refl_trans] at first second
  have hc := cancel_iso_middle (C l (ja ≫ h))
    (isoWhiskerRight (C ja h) (N l)) (C (l ≫ ja) h)
    (isoWhiskerLeft (N h) (C l ja))
    (isoWhiskerLeft (N h) (eqToIso (congrArg N sq) ≪≫ C jb m)) first.symm
  simpa only [isoWhiskerLeft_symm] using hc.trans second

private theorem combined_square_word {A₀ B₀ A₁ B₁ X : Scheme.{u}}
    (l : B₁ ⟶ B₀) (ja : B₀ ⟶ A₀) (jb : B₁ ⟶ A₁) (m : A₁ ⟶ A₀)
    (h : A₀ ⟶ X) (sq : l ≫ ja = jb ≫ m) (tot : l ≫ ja ≫ h = jb ≫ m ≫ h) :
    C l (ja ≫ h) ≪≫ isoWhiskerRight (C ja h) (N l) ≪≫
      isoWhiskerLeft (N h) ((C l ja).symm ≪≫
        eqToIso (congrArg N sq) ≪≫ C jb m) =
    (eqToIso (congrArg N tot) ≪≫ C jb (m ≫ h)) ≪≫
      isoWhiskerRight (C m h) (N jb) := by
  apply Iso.ext
  apply NatTrans.ext
  funext x
  have hx := congrArg (fun e ↦ e.hom.app x) (split_square_word l ja jb m h sq tot)
  simpa only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
    whiskerLeft_app, Category.assoc] using hx

/-- The geometric total equality determined by the two literal chart squares. -/
theorem total_square {X Y Z U V W : Scheme.{u}}
    (l : X ⟶ Y) (k : Y ⟶ Z) (ja : Z ⟶ U) (jc : Y ⟶ V)
    (jd : X ⟶ W) (m : W ⟶ V) (h : V ⟶ U)
    (sq₁ : k ≫ ja = jc ≫ h) (sq₂ : l ≫ jc = jd ≫ m) :
    (l ≫ k) ≫ ja = jd ≫ m ≫ h := by
  rw [Category.assoc, sq₁, ← Category.assoc l jc h, sq₂, Category.assoc]

/-- The exact raw cap-join word equals its prescribed Laurent triple normalization. -/
theorem raw_word {X Y Z U V W : Scheme.{u}}
    (l : X ⟶ Y) (k : Y ⟶ Z) (ja : Z ⟶ U) (jc : Y ⟶ V)
    (jd : X ⟶ W) (m : W ⟶ V) (h : V ⟶ U)
    (sq₁ : k ≫ ja = jc ≫ h) (sq₂ : l ≫ jc = jd ≫ m)
    (ht : (l ≫ k) ≫ ja = jd ≫ m ≫ h) :
    (isoWhiskerRight (C m h) (N jd) ≪≫
      (isoWhiskerLeft (N h) ((C l jc).symm ≪≫
        eqToIso (congrArg N sq₂) ≪≫ C jd m)).symm) ≪≫
      isoWhiskerRight ((C jc h).symm ≪≫
        eqToIso (congrArg N sq₁.symm) ≪≫ C k ja) (N l) =
    (C jd (m ≫ h)).symm ≪≫ eqToIso (congrArg N ht.symm) ≪≫
      C (l ≫ k) ja ≪≫ isoWhiskerLeft (N ja) (C l k) := by
  have tot : l ≫ jc ≫ h = jd ≫ m ≫ h :=
    (Category.assoc l jc h).symm.trans
      ((congrArg (fun f ↦ f ≫ h) sq₂).trans (Category.assoc jd m h))
  have hl : l ≫ jc ≫ h = (l ≫ k) ≫ ja :=
    (congrArg (fun f ↦ l ≫ f) sq₁.symm).trans (Category.assoc l k ja).symm
  have triple := anchored_factorizations_strict l k ja (l ≫ k) (jc ≫ h)
    (l ≫ jc ≫ h) rfl sq₁.symm hl rfl
  simp only [eqToIso_refl, Iso.refl_trans] at triple
  have hs := rearrange_square_word (C l (jc ≫ h))
    (isoWhiskerRight (C jc h) (N l))
    (isoWhiskerLeft (N h) ((C l jc).symm ≪≫
      eqToIso (congrArg N sq₂) ≪≫ C jd m))
    (eqToIso (congrArg N tot) ≪≫ C jd (m ≫ h))
    (isoWhiskerRight (C m h) (N jd))
    (isoWhiskerRight (eqToIso (congrArg N sq₁.symm) ≪≫ C k ja) (N l))
    (combined_square_word l jc jd m h sq₂ tot)
  calc
    _ = (eqToIso (congrArg N tot) ≪≫ C jd (m ≫ h)).symm ≪≫
        C l (jc ≫ h) ≪≫
        isoWhiskerRight (eqToIso (congrArg N sq₁.symm) ≪≫ C k ja) (N l) := by
      simpa only [isoWhiskerRight_trans, ← isoWhiskerRight_symm] using hs
    _ = (eqToIso (congrArg N tot) ≪≫ C jd (m ≫ h)).symm ≪≫
        eqToIso (congrArg N hl) ≪≫ C (l ≫ k) ja ≪≫
        isoWhiskerLeft (N ja) (C l k) := by
      exact congrArg (fun e ↦
        (eqToIso (congrArg N tot) ≪≫ C jd (m ≫ h)).symm ≪≫ e) triple.symm
    _ = _ := by
      have he : (eqToIso (congrArg N tot)).symm ≪≫ eqToIso (congrArg N hl) =
          eqToIso (congrArg N ht.symm) := by
        change eqToIso (congrArg N tot.symm) ≪≫ eqToIso (congrArg N hl) = _
        rw [eqToIso_trans]
      rw [Iso.trans_symm, Iso.trans_assoc,
        ← Iso.trans_assoc (eqToIso (congrArg N tot)).symm
          (eqToIso (congrArg N hl)), he]

/-- The small-model image retains the complete raw cap-join and Laurent triple words. -/
theorem small_word {X Y Z U V W : Scheme.{u}}
    (l : X ⟶ Y) (k : Y ⟶ Z) (ja : Z ⟶ U) (jc : Y ⟶ V)
    (jd : X ⟶ W) (m : W ⟶ V) (h : V ⟶ U)
    (sq₁ : k ≫ ja = jc ≫ h) (sq₂ : l ≫ jc = jd ≫ m)
    (ht : (l ≫ k) ≫ ja = jd ≫ m ≫ h) :
    (smallIso (isoWhiskerRight (C m h) (N jd)) ≪≫
      smallIso (isoWhiskerLeft (N h) ((C l jc).symm ≪≫
        eqToIso (congrArg N sq₂) ≪≫ C jd m)).symm) ≪≫
      smallIso (isoWhiskerRight ((C jc h).symm ≪≫
        eqToIso (congrArg N sq₁.symm) ≪≫ C k ja) (N l)) =
    (smallIso (C jd (m ≫ h))).symm ≪≫
      smallIso (eqToIso (congrArg N ht.symm)) ≪≫
      smallIso (C (l ≫ k) ja) ≪≫ smallIso (isoWhiskerLeft (N ja) (C l k)) := by
  have hs := congrArg smallIso (raw_word l k ja jc jd m h sq₁ sq₂ ht)
  simpa only [smallIso_trans, small_symm] using hs

/-- The same reference word at the actual normalized model functors and binary totals. -/
theorem model_word {X Y Z U V W : Scheme.{u}}
    (l : X ⟶ Y) (k : Y ⟶ Z) (ja : Z ⟶ U) (jc : Y ⟶ V)
    (jd : X ⟶ W) (m : W ⟶ V) (h : V ⟶ U)
    (sq₁ : k ≫ ja = jc ≫ h) (sq₂ : l ≫ jc = jd ≫ m)
    (ht : (l ≫ k) ≫ ja = jd ≫ m ≫ h) :
    ((isoWhiskerRight (BinaryNormalizationSimplex.total m h) (normalizedMap jd).functor ≪≫
      (isoWhiskerLeft (normalizedMap h).functor
        ((BinaryNormalizationSimplex.total l jc).symm ≪≫
          smallIso (eqToIso (congrArg N sq₂)) ≪≫
          BinaryNormalizationSimplex.total jd m)).symm) ≪≫
      isoWhiskerRight ((BinaryNormalizationSimplex.total jc h).symm ≪≫
        smallIso (eqToIso (congrArg N sq₁.symm)) ≪≫
        BinaryNormalizationSimplex.total k ja) (normalizedMap l).functor :
      (normalizedMap (m ≫ h) ≫ normalizedMap jd).functor ≅
        ((normalizedMap ja ≫ normalizedMap k) ≫ normalizedMap l).functor) =
    (BinaryNormalizationSimplex.total jd (m ≫ h)).symm ≪≫
      smallIso (eqToIso (congrArg N ht.symm)) ≪≫
      BinaryNormalizationSimplex.total (l ≫ k) ja ≪≫
      isoWhiskerLeft (normalizedMap ja).functor (BinaryNormalizationSimplex.total l k) := by
  exact transport_model_word (N l) (N k) (N ja) (N jc) (N jd) (N m) (N h)
    (C m h) (C l jc) (eqToIso (congrArg N sq₂)) (C jd m)
    (C jc h) (eqToIso (congrArg N sq₁.symm)) (C k ja)
    (C jd (m ≫ h)) (eqToIso (congrArg N ht.symm)) (C (l ≫ k) ja) (C l k)
    (raw_word l k ja jc jd m h sq₁ sq₂ ht)

end Quillen.PerfectComplexes.CoefficientBassCapChartTripleWord
