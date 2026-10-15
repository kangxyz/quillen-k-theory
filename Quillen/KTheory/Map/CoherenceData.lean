/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Basic
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Quillen.KTheory.Map.Basic

/-!
# Algebraic comparison data for composition of zero-based K-maps

These results concern isomorphisms of Q-objects and rebased functors.
They do not assert equality of K-group maps without a realization theorem
for homotopies that fix the basepoint.
-/
@[expose] public section

open CategoryTheory.ExactCategory



noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace Quillen

section QIsomorphisms

variable {C : Type u} [Category.{v} C]
  (deflation inflation : MorphismProperty C)
  [deflation.ContainsIdentities] [inflation.ContainsIdentities]
  [deflation.IsStableUnderComposition] [inflation.IsStableUnderComposition]
  [deflation.HasPullbacksAgainst inflation]
  [deflation.IsStableUnderBaseChangeAgainst inflation]
  [inflation.IsStableUnderBaseChangeAgainst deflation]

set_option backward.isDefEq.respectTransparency false in
/-- Multiplying the identity-left-leg spans of two isomorphisms gives the span
of their composite, up to the canonical pullback-apex isomorphism. -/
def Q.isoSpanCompToIso {X Y Z : C} (e : X ≅ Y) (f : Y ≅ Z)
    (he : inflation e.hom) (hf : inflation f.hom) (hef : inflation (e ≪≫ f).hom) :
    Span.comp (Q.isoSpan deflation inflation e he)
      (Q.isoSpan deflation inflation f hf) ≅ Q.isoSpan deflation inflation (e ≪≫ f) hef := by
  let s := Q.isoSpan deflation inflation e he
  let t := Q.isoSpan deflation inflation f hf
  letI : HasPullback s.r t.l := inferInstance
  letI : IsIso t.l := inferInstanceAs (IsIso (𝟙 Y))
  letI : IsIso (pullback.fst s.r t.l) :=
    (IsPullback.of_hasPullback s.r t.l).isIso_fst_of_isIso
  refine Span.mkIso (asIso (pullback.fst s.r t.l)) ?_ ?_
  · simp [s, t, Q.isoSpan, Span.comp]
  · change pullback.fst s.r t.l ≫ (e.hom ≫ f.hom) = pullback.snd s.r t.l ≫ f.hom
    have h := pullback.condition (f := s.r) (g := t.l)
    dsimp only [s, t, Q.isoSpan] at h ⊢
    simpa only [Category.assoc, Category.comp_id] using congrArg (fun k => k ≫ f.hom) h

/-- The Q-isomorphism construction preserves composition. -/
theorem Q.isoOfIso_trans {X Y Z : C} (e : X ≅ Y) (f : Y ≅ Z)
    (he : inflation e.hom) (he' : inflation e.inv)
    (hf : inflation f.hom) (hf' : inflation f.inv)
    (hef : inflation (e ≪≫ f).hom) (hef' : inflation (e ≪≫ f).inv) :
    Q.isoOfIso deflation inflation (e ≪≫ f) hef hef' =
      Q.isoOfIso deflation inflation e he he' ≪≫
        Q.isoOfIso deflation inflation f hf hf' := by
  apply Iso.ext
  symm
  exact Quotient.sound ⟨Q.isoSpanCompToIso deflation inflation e f he hf hef⟩

end QIsomorphisms

section ExactQIsomorphisms

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [HasFiniteBiproducts C] [Preadditive D] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D}

/-- Original isomorphism composition is respected in an exact Q-category. -/
@[simp]
theorem _root_.CategoryTheory.ExactCategory.ExactStructure.qIsoOfIso_trans (E : ExactStructure C)
    {X Y Z : C} (e : X ≅ Y) (f : Y ≅ Z) :
    E.qIsoOfIso (e ≪≫ f) = E.qIsoOfIso e ≪≫ E.qIsoOfIso f :=
  Q.isoOfIso_trans E.deflation E.inflation e f _ _ _ _ _ _

/-- An exact functor's Q-functor takes the Q-isomorphism of an original
isomorphism to the Q-isomorphism of its image. -/
@[simp]
theorem _root_.CategoryTheory.ExactCategory.ExactFunctor.mapQ_qIsoOfIso (F : ExactFunctor EC ED)
    {X Y : C} (e : X ≅ Y) :
    F.mapQ.mapIso (EC.qIsoOfIso e) = ED.qIsoOfIso (F.toFunctor.mapIso e) := by
  apply Iso.ext
  apply Quotient.sound
  refine ⟨Span.mkIso (Iso.refl _) ?_ ?_⟩
  · change 𝟙 (F.toFunctor.obj X) ≫ 𝟙 (F.toFunctor.obj X) = F.toFunctor.map (𝟙 X)
    simp
  · change 𝟙 (F.toFunctor.obj X) ≫ F.toFunctor.map e.hom = F.toFunctor.map e.hom
    simp

end ExactQIsomorphisms

section RebaseComposition

variable {C D T : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} T]

/-- The base component of the normalization is precisely the supplied
isomorphism, with the object equality made explicit. -/
theorem rebaseFunctorIso_hom_base (F : C ⥤ D) (c : C) (d : D) (e : F.obj c ≅ d) :
    (rebaseFunctorIso F c d e).hom.app c =
      e.hom ≫ eqToHom (rebaseFunctor_obj_base F c d e).symm := by
  classical
  dsimp only [rebaseFunctorIso, NatIso.ofComponents, rebaseObjIso]
  simp
  rfl

/-- The composite of two rebased functors sends the chosen base object to the
chosen final base object. -/
theorem rebaseFunctor_comp_obj_base (F : C ⥤ D) (G : D ⥤ T)
    (c : C) (d : D) (t : T) (e : F.obj c ≅ d) (f : G.obj d ≅ t) :
    ((rebaseFunctor F c d e) ⋙ rebaseFunctor G d t f).obj c = t :=
  (congrArg (rebaseFunctor G d t f).obj (rebaseFunctor_obj_base F c d e)).trans
    (rebaseFunctor_obj_base G d t f)

/-- Comparison from the original composite to the composite of its two
normalized functors. -/
def rebaseFunctorCompRightIso (F : C ⥤ D) (G : D ⥤ T)
    (c : C) (d : D) (t : T) (e : F.obj c ≅ d) (f : G.obj d ≅ t) :
    F ⋙ G ≅ (rebaseFunctor F c d e) ⋙ rebaseFunctor G d t f :=
  Functor.isoWhiskerRight (rebaseFunctorIso F c d e) G ≪≫
    Functor.isoWhiskerLeft (rebaseFunctor F c d e) (rebaseFunctorIso G d t f)

/-- At the base object, the comparison to the composite of normalized
functors is exactly the composite of the two specified base isomorphisms. -/
theorem rebaseFunctorCompRightIso_hom_base (F : C ⥤ D) (G : D ⥤ T)
    (c : C) (d : D) (t : T) (e : F.obj c ≅ d) (f : G.obj d ≅ t) :
    (rebaseFunctorCompRightIso F G c d t e f).hom.app c ≫
      eqToHom (rebaseFunctor_comp_obj_base F G c d t e f) = G.map e.hom ≫ f.hom := by
  have hn := (rebaseFunctorIso G d t f).hom.naturality
    (eqToHom (rebaseFunctor_obj_base F c d e))
  dsimp only [rebaseFunctorCompRightIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  rw [rebaseFunctorIso_hom_base, G.map_comp]
  have hb : eqToHom (rebaseFunctor_comp_obj_base F G c d t e f) =
      (rebaseFunctor G d t f).map (eqToHom (rebaseFunctor_obj_base F c d e)) ≫
        eqToHom (rebaseFunctor_obj_base G d t f) := by
    simp only [eqToHom_map, eqToHom_trans]
  rw [hb]
  simp only [Category.assoc]
  rw [← Category.assoc ((rebaseFunctorIso G d t f).hom.app _), ← hn,
    rebaseFunctorIso_hom_base]
  simp [eqToHom_map]


/-- The natural comparison between normalizing a composite and composing the
two normalized functors. -/
def rebaseFunctorCompIso (F : C ⥤ D) (G : D ⥤ T)
    (c : C) (d : D) (t : T) (e : F.obj c ≅ d) (f : G.obj d ≅ t) :
    rebaseFunctor (F ⋙ G) c t (G.mapIso e ≪≫ f) ≅
      (rebaseFunctor F c d e) ⋙ rebaseFunctor G d t f :=
  (rebaseFunctorIso (F ⋙ G) c t (G.mapIso e ≪≫ f)).symm ≪≫
    rebaseFunctorCompRightIso F G c d t e f

/-- The two normalized composites have the same base object. -/
theorem rebaseFunctorCompIso_obj_base (F : C ⥤ D) (G : D ⥤ T)
    (c : C) (d : D) (t : T) (e : F.obj c ≅ d) (f : G.obj d ≅ t) :
    (rebaseFunctor (F ⋙ G) c t (G.mapIso e ≪≫ f)).obj c =
      ((rebaseFunctor F c d e) ⋙ rebaseFunctor G d t f).obj c :=
  (rebaseFunctor_obj_base (F ⋙ G) c t (G.mapIso e ≪≫ f)).trans
    (rebaseFunctor_comp_obj_base F G c d t e f).symm

/-- The natural comparison fixes the base object: its component is the
identity after the displayed object equality. This is the exact input needed
by the based nerve-cylinder theorem. -/
theorem rebaseFunctorCompIso_hom_base (F : C ⥤ D) (G : D ⥤ T)
    (c : C) (d : D) (t : T) (e : F.obj c ≅ d) (f : G.obj d ≅ t) :
    (rebaseFunctorCompIso F G c d t e f).hom.app c =
      eqToHom (rebaseFunctorCompIso_obj_base F G c d t e f) := by
  apply (cancel_mono (eqToHom (rebaseFunctor_comp_obj_base F G c d t e f))).mp
  dsimp only [rebaseFunctorCompIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [Category.assoc, rebaseFunctorCompRightIso_hom_base]
  have hh : (rebaseFunctorIso (F ⋙ G) c t (G.mapIso e ≪≫ f)).hom.app c ≫
      eqToHom (rebaseFunctor_obj_base (F ⋙ G) c t (G.mapIso e ≪≫ f)) =
      G.map e.hom ≫ f.hom := by
    rw [rebaseFunctorIso_hom_base]
    simp
  rw [← hh]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp, eqToHom_trans]


/-- Rebasing is unchanged by equal functors and the corresponding equal
base isomorphisms. -/
theorem rebaseFunctor_congr {F G : C ⥤ D} (h : F = G) (c : C) (d : D)
    (e : F.obj c ≅ d) (f : G.obj c ≅ d) (he : HEq e f) :
    rebaseFunctor F c d e = rebaseFunctor G c d f := by
  subst G
  obtain rfl := eq_of_heq he
  rfl


/-- Transporting the source functor of a based comparison preserves its
identity base component. -/
theorem eqToIso_trans_hom_base {F G H : C ⥤ D} (h : F = G) (e : G ≅ H)
    (c : C) (hc : G.obj c = H.obj c) (he : e.hom.app c = eqToHom hc) :
    (eqToIso h ≪≫ e).hom.app c =
      eqToHom ((congrArg (fun K : C ⥤ D => K.obj c) h).trans hc) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app, he, eqToHom_trans]


end RebaseComposition

section ExactRebaseComposition

open scoped ZeroObject

variable {C D T : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} T]
  [Preadditive C] [HasFiniteBiproducts C] [Preadditive D] [HasFiniteBiproducts D]
  [Preadditive T] [HasFiniteBiproducts T]
  {EC : ExactStructure C} {ED : ExactStructure D} {ET : ExactStructure T}

set_option backward.isDefEq.respectTransparency false in
/-- Canonical zero-object isomorphisms obey composition after passage to Q. -/
theorem _root_.CategoryTheory.ExactCategory.ExactFunctor.comp_qZeroIso (F : ExactFunctor EC ED) (G :
  ExactFunctor ED ET) :
    ET.qIsoOfIso (F.comp G).toFunctor.mapZeroObject =
      G.mapQ.mapIso (ED.qIsoOfIso F.toFunctor.mapZeroObject) ≪≫
        ET.qIsoOfIso G.toFunctor.mapZeroObject := by
  have hz : (F.comp G).toFunctor.mapZeroObject =
      G.toFunctor.mapIso F.toFunctor.mapZeroObject ≪≫ G.toFunctor.mapZeroObject := by
    apply Iso.ext
    apply Subsingleton.elim
  calc
    ET.qIsoOfIso (F.comp G).toFunctor.mapZeroObject =
        ET.qIsoOfIso (G.toFunctor.mapIso F.toFunctor.mapZeroObject ≪≫
          G.toFunctor.mapZeroObject) := congrArg ET.qIsoOfIso hz
    _ = ET.qIsoOfIso (G.toFunctor.mapIso F.toFunctor.mapZeroObject) ≪≫
        ET.qIsoOfIso G.toFunctor.mapZeroObject := ET.qIsoOfIso_trans _ _
    _ = G.mapQ.mapIso (ED.qIsoOfIso F.toFunctor.mapZeroObject) ≪≫
        ET.qIsoOfIso G.toFunctor.mapZeroObject := by
      rw [CategoryTheory.ExactCategory.ExactFunctor.mapQ_qIsoOfIso]


/-- The Q-functor normalized at the chosen zero objects. Its realization
is the continuous map used in `CategoryTheory.ExactCategory.ExactFunctor.KMap`. -/
def _root_.CategoryTheory.ExactCategory.ExactFunctor.normalizedQ (F : ExactFunctor EC ED) :
  EC.QCategory ⥤ ED.QCategory :=
  rebaseFunctor F.mapQ (Q.of EC.deflation EC.inflation (0 : C))
    (Q.of ED.deflation ED.inflation (0 : D)) (ED.qIsoOfIso F.toFunctor.mapZeroObject)

/-- The normalized Q-functor of an exact composite is the generic rebasing
of the composite Q-functor with its compositional base isomorphism. -/
theorem _root_.CategoryTheory.ExactCategory.ExactFunctor.normalizedQ_comp_eq (F : ExactFunctor EC
  ED) (G : ExactFunctor ED ET) :
    (F.comp G).normalizedQ =
      rebaseFunctor (F.mapQ ⋙ G.mapQ) (Q.of EC.deflation EC.inflation (0 : C))
        (Q.of ET.deflation ET.inflation (0 : T))
        (G.mapQ.mapIso (ED.qIsoOfIso F.toFunctor.mapZeroObject) ≪≫
          ET.qIsoOfIso G.toFunctor.mapZeroObject) :=
  rebaseFunctor_congr (F.mapQ_comp G) _ _ _ _ (heq_of_eq (F.comp_qZeroIso G))

/-- The comparison natural isomorphism for the actual normalized Q-functors
used by KMap. -/
def _root_.CategoryTheory.ExactCategory.ExactFunctor.normalizedQCompIso (F : ExactFunctor EC ED) (G
  : ExactFunctor ED ET) :
    (F.comp G).normalizedQ ≅ F.normalizedQ ⋙ G.normalizedQ :=
  eqToIso (F.normalizedQ_comp_eq G) ≪≫
    rebaseFunctorCompIso F.mapQ G.mapQ
      (Q.of EC.deflation EC.inflation (0 : C))
      (Q.of ED.deflation ED.inflation (0 : D))
      (Q.of ET.deflation ET.inflation (0 : T))
      (ED.qIsoOfIso F.toFunctor.mapZeroObject) (ET.qIsoOfIso G.toFunctor.mapZeroObject)

/-- The two normalized exact composites have equal chosen base objects. -/
theorem _root_.CategoryTheory.ExactCategory.ExactFunctor.normalizedQCompIso_obj_base
    (F : ExactFunctor EC ED) (G : ExactFunctor ED ET) :
    (F.comp G).normalizedQ.obj (Q.of EC.deflation EC.inflation (0 : C)) =
      (F.normalizedQ ⋙ G.normalizedQ).obj (Q.of EC.deflation EC.inflation (0 : C)) :=
  (congrArg (fun H : EC.QCategory ⥤ ET.QCategory =>
      H.obj (Q.of EC.deflation EC.inflation (0 : C))) (F.normalizedQ_comp_eq G)).trans
    (rebaseFunctorCompIso_obj_base F.mapQ G.mapQ
      (Q.of EC.deflation EC.inflation (0 : C))
      (Q.of ED.deflation ED.inflation (0 : D))
      (Q.of ET.deflation ET.inflation (0 : T))
      (ED.qIsoOfIso F.toFunctor.mapZeroObject) (ET.qIsoOfIso G.toFunctor.mapZeroObject))

/-- The comparison for exact functors fixes zero: its component is identity
under the equality of the chosen base objects. -/
theorem _root_.CategoryTheory.ExactCategory.ExactFunctor.normalizedQCompIso_hom_base
    (F : ExactFunctor EC ED) (G : ExactFunctor ED ET) :
    (F.normalizedQCompIso G).hom.app (Q.of EC.deflation EC.inflation (0 : C)) =
      eqToHom (F.normalizedQCompIso_obj_base G) :=
  eqToIso_trans_hom_base (F.normalizedQ_comp_eq G) _ _ _
    (rebaseFunctorCompIso_hom_base F.mapQ G.mapQ
      (Q.of EC.deflation EC.inflation (0 : C))
      (Q.of ED.deflation ED.inflation (0 : D))
      (Q.of ET.deflation ET.inflation (0 : T))
      (ED.qIsoOfIso F.toFunctor.mapZeroObject) (ET.qIsoOfIso G.toFunctor.mapZeroObject))


end ExactRebaseComposition

end Quillen
