/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.CategoryTheory.QConstruction.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
# Functoriality of the restricted-span Q-construction

A functor that preserves the two admissibility properties and the mixed
pullbacks induces a functor of Q-categories. The morphism map is the map on
actual span representatives, descended through the apex-isomorphism quotient.
Its composition law uses the canonical pullback comparison isomorphism.

The selective pullback hypothesis below is explicit. `Quillen.ExactFunctor`
derives it from additivity and preservation of conflations.
-/
@[expose] public section


noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory CategoryTheory.Limits

namespace Quillen

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

/-- Precisely the functorial hypotheses needed by restricted-span composition.
Only pullbacks of an admissible monomorphism against an admissible epimorphism
are required to be preserved. -/
structure QCompatibleFunctor (deflationC inflationC : MorphismProperty C)
    (deflationD inflationD : MorphismProperty D) where
  /-- The underlying functor of the original categories. -/
  toFunctor : C ⥤ D
  /-- Admissible epimorphisms map to admissible epimorphisms. -/
  map_deflation : ∀ {X Y : C} (f : X ⟶ Y), deflationC f → deflationD (toFunctor.map f)
  /-- Admissible monomorphisms map to admissible monomorphisms. -/
  map_inflation : ∀ {X Y : C} (f : X ⟶ Y), inflationC f → inflationD (toFunctor.map f)
  /-- Preservation of the mixed pullbacks used to compose Q-morphisms. -/
  preserves_mixed : ∀ {A B T : C} (i : A ⟶ T) (p : B ⟶ T),
    inflationC i → deflationC p → PreservesLimit (cospan i p) toFunctor

namespace QCompatibleFunctor

/-- The identity functor satisfies the Q-compatibility conditions. -/
def id (deflation inflation : MorphismProperty C) :
    QCompatibleFunctor deflation inflation deflation inflation where
  toFunctor := 𝟭 C
  map_deflation _ h := h
  map_inflation _ h := h
  preserves_mixed _ _ _ _ := inferInstance

/-- Any functor preserving all pullbacks and both leg properties is Q-compatible.
This convenient adapter imposes a stronger preservation condition than necessary. -/
def ofPreservesPullbacks
    (deflationC inflationC : MorphismProperty C)
    (deflationD inflationD : MorphismProperty D)
    (F : C ⥤ D) [PreservesLimitsOfShape WalkingCospan F]
    (hd : ∀ {X Y : C} (f : X ⟶ Y), deflationC f → deflationD (F.map f))
    (hi : ∀ {X Y : C} (f : X ⟶ Y), inflationC f → inflationD (F.map f)) :
    QCompatibleFunctor deflationC inflationC deflationD inflationD where
  toFunctor := F
  map_deflation := hd
  map_inflation := hi
  preserves_mixed _ _ _ _ := inferInstance

/-- Q-compatible functors compose. Selective preservation suffices because the
first functor preserves the admissibility of the two maps in each cospan. -/
def comp {E : Type u₃} [Category.{v₃} E]
    {deflationC inflationC : MorphismProperty C}
    {deflationD inflationD : MorphismProperty D}
    {deflationE inflationE : MorphismProperty E}
    (F : QCompatibleFunctor deflationC inflationC deflationD inflationD)
    (G : QCompatibleFunctor deflationD inflationD deflationE inflationE) :
    QCompatibleFunctor deflationC inflationC deflationE inflationE where
  toFunctor := F.toFunctor ⋙ G.toFunctor
  map_deflation f h := G.map_deflation _ (F.map_deflation f h)
  map_inflation f h := G.map_inflation _ (F.map_inflation f h)
  preserves_mixed i p hi hp := by
    let : PreservesLimit (cospan i p) F.toFunctor := F.preserves_mixed i p hi hp
    let : PreservesLimit (cospan (F.toFunctor.map i) (F.toFunctor.map p)) G.toFunctor :=
      G.preserves_mixed _ _ (F.map_inflation i hi) (F.map_deflation p hp)
    let : PreservesLimit (cospan i p ⋙ F.toFunctor) G.toFunctor :=
      preservesLimit_of_iso_diagram G.toFunctor (cospanCompIso F.toFunctor i p).symm
    infer_instance

variable {deflationC inflationC : MorphismProperty C}
  {deflationD inflationD : MorphismProperty D}
  (F : QCompatibleFunctor deflationC inflationC deflationD inflationD)

/-- Map a span by applying the underlying functor to its apex and both legs. -/
def mapSpan {X Y : C} (s : Span deflationC inflationC X Y) :
    Span deflationD inflationD (F.toFunctor.obj X) (F.toFunctor.obj Y) where
  apex := F.toFunctor.obj s.apex
  l := F.toFunctor.map s.l
  r := F.toFunctor.map s.r
  wl := F.map_deflation s.l s.wl
  wr := F.map_inflation s.r s.wr

/-- An apex isomorphism of source spans maps to an apex isomorphism of target spans. -/
def mapSpanIso {X Y : C} {s t : Span deflationC inflationC X Y} (e : s ≅ t) :
    F.mapSpan s ≅ F.mapSpan t :=
  Span.mkIso (F.toFunctor.mapIso
    { hom := e.hom.hom
      inv := e.inv.hom
      hom_inv_id := congrArg Span.Hom.hom e.hom_inv_id
      inv_hom_id := congrArg Span.Hom.hom e.inv_hom_id })
    (by simpa only [mapSpan, Functor.mapIso_hom, ← Functor.map_comp] using
      congrArg F.toFunctor.map e.hom.hom_l)
    (by simpa only [mapSpan, Functor.mapIso_hom, ← Functor.map_comp] using
      congrArg F.toFunctor.map e.hom.hom_r)

variable [deflationC.ContainsIdentities] [inflationC.ContainsIdentities]
  [deflationC.IsStableUnderComposition] [inflationC.IsStableUnderComposition]
  [deflationC.HasPullbacksAgainst inflationC]
  [deflationC.IsStableUnderBaseChangeAgainst inflationC]
  [inflationC.IsStableUnderBaseChangeAgainst deflationC]
  [deflationD.ContainsIdentities] [inflationD.ContainsIdentities]
  [deflationD.IsStableUnderComposition] [inflationD.IsStableUnderComposition]
  [deflationD.HasPullbacksAgainst inflationD]
  [deflationD.IsStableUnderBaseChangeAgainst inflationD]
  [inflationD.IsStableUnderBaseChangeAgainst deflationD]

/-- Mapping the identity span gives a span isomorphic to the identity span. -/
def mapSpanIdIso (X : C) :
    F.mapSpan (Span.id X) ≅ Span.id (F.toFunctor.obj X) :=
  Span.mkIso (Iso.refl _) (by simp [mapSpan]) (by simp [mapSpan])

/-- The comparison isomorphism for span composition has as its apex map the
canonical isomorphism from the image pullback to the pullback of the images. -/
def mapSpanCompIso {X Y Z : C} (s : Span deflationC inflationC X Y)
    (t : Span deflationC inflationC Y Z) :
    F.mapSpan (Span.comp s t) ≅ Span.comp (F.mapSpan s) (F.mapSpan t) := by
  letI : PreservesLimit (cospan s.r t.l) F.toFunctor :=
    F.preserves_mixed s.r t.l s.wr t.wl
  letI : HasPullback (F.toFunctor.map s.r) (F.toFunctor.map t.l) :=
    inferInstanceAs (HasPullback (F.mapSpan s).r (F.mapSpan t).l)
  refine Span.mkIso (PreservesPullback.iso F.toFunctor s.r t.l) ?_ ?_
  · dsimp only [mapSpan, Span.comp]
    rw [← Category.assoc, PreservesPullback.iso_hom_fst, Functor.map_comp]
  · dsimp only [mapSpan, Span.comp]
    rw [← Category.assoc, PreservesPullback.iso_hom_snd, Functor.map_comp]

/-- The induced functor of Q-categories. All quotient relations are respected
by mapped apex isomorphisms. -/
def mapQ : Q deflationC inflationC ⥤ Q deflationD inflationD where
  obj X := Q.of deflationD inflationD (F.toFunctor.obj X.obj.of)
  map := Quotient.map (fun s => F.mapSpan s) (fun _ _ h => by
    obtain ⟨e⟩ := h
    exact ⟨F.mapSpanIso e⟩)
  map_id X := Quotient.sound ⟨F.mapSpanIdIso X.obj.of⟩
  map_comp := by
    rintro X Y Z ⟨s⟩ ⟨t⟩
    exact Quotient.sound ⟨F.mapSpanCompIso s t⟩

/-- The induced object map is the original functor's object map. -/
@[simp]
theorem mapQ_obj_of (X : C) :
    F.mapQ.obj (Q.of deflationC inflationC X) =
      Q.of deflationD inflationD (F.toFunctor.obj X) := rfl

/-- On Q-morphism representatives the induced map applies the functor to both legs. -/
@[simp]
theorem mapQ_mkHom {X Y : C} (s : Span deflationC inflationC X Y) :
    F.mapQ.map (Q.mkHom deflationC inflationC s) =
      Q.mkHom deflationD inflationD (F.mapSpan s) := rfl

/-- The Q-construction sends the identity compatible functor to the identity functor. -/
@[simp]
theorem mapQ_id :
    (id deflationC inflationC).mapQ = 𝟭 (Q deflationC inflationC) := by
  refine Functor.hext ?_ ?_
  · intro X
    rfl
  · rintro X Y ⟨s⟩
    rfl

variable {E : Type u₃} [Category.{v₃} E]
  {deflationE inflationE : MorphismProperty E}
  [deflationE.ContainsIdentities] [inflationE.ContainsIdentities]
  [deflationE.IsStableUnderComposition] [inflationE.IsStableUnderComposition]
  [deflationE.HasPullbacksAgainst inflationE]
  [deflationE.IsStableUnderBaseChangeAgainst inflationE]
  [inflationE.IsStableUnderBaseChangeAgainst deflationE]

/-- The Q-construction sends the composition of compatible functors to the
composition of their induced Q-functors. -/
@[simp]
theorem mapQ_comp (G : QCompatibleFunctor deflationD inflationD deflationE inflationE) :
    (F.comp G).mapQ = F.mapQ ⋙ G.mapQ := by
  refine Functor.hext ?_ ?_
  · intro X
    rfl
  · rintro X Y ⟨s⟩
    rfl

end QCompatibleFunctor

end Quillen
