/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.HomotopyGroups.Map
public import Quillen.CategoryTheory.QConstruction.Functor
public import Quillen.KTheory.Basic
public import Quillen.CategoryTheory.ExactCategory.Isomorphisms
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso

/-!
# Functors rebased at a chosen object

A functor together with an isomorphism from the image of the source base object
to the target base object can be replaced by a naturally isomorphic functor that
sends the source base object exactly to the target base object. Its classifying
space map is pointed, so it induces genuine homomorphisms between the shifted
homotopy groups at the specified base objects.

This construction uses the supplied isomorphism. Independence from this choice,
and compatibility with a separate path-transport construction, are not claimed.
-/
@[expose] public section


noncomputable section

open CategoryTheory

universe v u

namespace Quillen

variable {C : Type u} {D : Type u} [Category.{v} C] [Category.{v} D]

/-- Replace the image of one specified object by the desired target object. -/
def rebaseObj (F : C ⥤ D) (c : C) (d : D) (X : C) : D :=
  by
    classical
    exact if X = c then d else F.obj X

/-- The pointwise comparison with the original object map. -/
def rebaseObjIso (F : C ⥤ D) (c : C) (d : D) (e : F.obj c ≅ d) (X : C) :
    F.obj X ≅ rebaseObj F c d X := by
  classical
  exact if h : X = c then
    eqToIso (congrArg F.obj h) ≪≫ e ≪≫ eqToIso (by simp [rebaseObj, h])
  else
    eqToIso (by simp [rebaseObj, h])

/-- Conjugate the original arrow map by the chosen objectwise isomorphisms. -/
def rebaseFunctor (F : C ⥤ D) (c : C) (d : D) (e : F.obj c ≅ d) : C ⥤ D where
  obj := rebaseObj F c d
  map {X Y} f := (rebaseObjIso F c d e X).inv ≫ F.map f ≫
    (rebaseObjIso F c d e Y).hom
  map_id X := by simp
  map_comp f g := by simp [Category.assoc]

/-- Rebasing gives a naturally isomorphic functor. -/
def rebaseFunctorIso (F : C ⥤ D) (c : C) (d : D) (e : F.obj c ≅ d) :
    F ≅ rebaseFunctor F c d e :=
  NatIso.ofComponents (rebaseObjIso F c d e) (by
    intros X Y f
    simp [rebaseFunctor])

/-- The rebased functor takes the source base object to the target base object. -/
@[simp]
theorem rebaseFunctor_obj_base (F : C ⥤ D) (c : C) (d : D) (e : F.obj c ≅ d) :
    (rebaseFunctor F c d e).obj c = d := by
  classical
  simp [rebaseFunctor, rebaseObj]

/-- Rebasing along the reflexive isomorphism leaves the functor unchanged. -/
@[simp]
theorem rebaseFunctor_refl (F : C ⥤ D) (c : C) :
    rebaseFunctor F c (F.obj c) (Iso.refl _) = F := by
  classical
  have hobj (X : C) : (rebaseFunctor F c (F.obj c) (Iso.refl _)).obj X = F.obj X := by
    by_cases h : X = c
    · subst X
      simp [rebaseFunctor, rebaseObj]
    · simp [rebaseFunctor, rebaseObj, h]
  refine Functor.ext_of_iso (rebaseFunctorIso F c (F.obj c) (Iso.refl _)).symm hobj ?_
  intro X
  dsimp only [rebaseFunctorIso, NatIso.ofComponents, Iso.symm, rebaseObjIso]
  split_ifs with h
  · subst X
    simp
    rfl
  · rfl


/-- Realization of the rebased functor preserves the specified basepoints. -/
theorem rebaseFunctor_map_point (F : C ⥤ D) (c : C) (d : D) (e : F.obj c ≅ d) :
    classifyingSpaceMap (rebaseFunctor F c d e) (classifyingSpacePoint c) =
      classifyingSpacePoint d := by
  rw [classifyingSpaceMap_point, rebaseFunctor_obj_base]

/-- The genuine homomorphism between shifted homotopy groups at prescribed
base objects, associated to a functor and a specified base-object isomorphism. -/
def pointedShiftedHomotopyGroupMap (F : C ⥤ D) (c : C) (d : D)
    (e : F.obj c ≅ d) (n : ℕ) :
    ShiftedHomotopyGroup C c n →* ShiftedHomotopyGroup D d n :=
  piMap n (classifyingSpaceMap (rebaseFunctor F c d e)).hom
    (rebaseFunctor_map_point F c d e)

set_option backward.isDefEq.respectTransparency false in
/-- The pointed construction preserves the identity functor. -/
@[simp]
theorem pointedShiftedHomotopyGroupMap_id (c : C) (n : ℕ) :
    pointedShiftedHomotopyGroupMap (𝟭 C) c c (Iso.refl c) n =
      MonoidHom.id (ShiftedHomotopyGroup C c n) := by
  have hF : rebaseFunctor (𝟭 C) c c (Iso.refl c) = 𝟭 C :=
    rebaseFunctor_refl (𝟭 C) c
  have hT : classifyingSpaceMap (rebaseFunctor (𝟭 C) c c (Iso.refl c)) =
      𝟙 (ClassifyingSpace C) := by rw [hF, classifyingSpaceMap_id]
  apply MonoidHom.ext
  intro a
  change homotopyGroupMap (classifyingSpaceMap (rebaseFunctor (𝟭 C) c c (Iso.refl c))).hom
    (rebaseFunctor_map_point (𝟭 C) c c (Iso.refl c)) a = a
  simpa only [hT, TopCat.hom_id] using homotopyGroupMap_id a


section QIsomorphisms

open CategoryTheory.Limits

variable (deflation inflation : MorphismProperty C)
  [deflation.ContainsIdentities] [inflation.ContainsIdentities]
  [deflation.IsStableUnderComposition] [inflation.IsStableUnderComposition]
  [deflation.HasPullbacksAgainst inflation]
  [deflation.IsStableUnderBaseChangeAgainst inflation]
  [inflation.IsStableUnderBaseChangeAgainst deflation]

/-- The identity-left-leg span of an admissible arrow. -/
def Q.isoSpan {X Y : C} (e : X ≅ Y) (he : inflation e.hom) :
    Span deflation inflation X Y where
  apex := X
  l := 𝟙 X
  r := e.hom
  wl := MorphismProperty.ContainsIdentities.id_mem X
  wr := he

set_option backward.isDefEq.respectTransparency false in
/-- The composite of the two spans associated to an isomorphism and its inverse
is isomorphic to the identity span, using the actual pullback projection. -/
def Q.isoSpanCompIso {X Y : C} (e : X ≅ Y)
    (he : inflation e.hom) (hi : inflation e.inv) :
    Span.comp (Q.isoSpan deflation inflation e he)
      (Q.isoSpan deflation inflation e.symm hi) ≅ Span.id X := by
  let s := Q.isoSpan deflation inflation e he
  let t := Q.isoSpan deflation inflation e.symm hi
  letI : HasPullback s.r t.l := inferInstance
  letI : IsIso t.l := inferInstanceAs (IsIso (𝟙 Y))
  letI : IsIso (pullback.fst s.r t.l) :=
    (IsPullback.of_hasPullback s.r t.l).isIso_fst_of_isIso
  refine Span.mkIso (asIso (pullback.fst s.r t.l)) ?_ ?_
  · simp [s, t, Q.isoSpan, Span.comp]
  · change pullback.fst s.r t.l ≫ 𝟙 X = pullback.snd s.r t.l ≫ e.inv
    have h := pullback.condition (f := s.r) (g := t.l)
    change pullback.fst s.r t.l ≫ e.hom = pullback.snd s.r t.l ≫ 𝟙 Y at h
    dsimp only [s, t, Q.isoSpan] at h ⊢
    simpa only [Category.assoc, e.hom_inv_id, Category.comp_id, Category.id_comp]
      using congrArg (fun k => k ≫ e.inv) h


/-- An original-category isomorphism, with admissible forward and inverse maps,
induces an isomorphism of Q-objects. -/
def Q.isoOfIso {X Y : C} (e : X ≅ Y)
    (he : inflation e.hom) (hi : inflation e.inv) :
    Q.of deflation inflation X ≅ Q.of deflation inflation Y where
  hom := Q.mkHom deflation inflation (Q.isoSpan deflation inflation e he)
  inv := Q.mkHom deflation inflation (Q.isoSpan deflation inflation e.symm hi)
  hom_inv_id := Quotient.sound ⟨Q.isoSpanCompIso deflation inflation e he hi⟩
  inv_hom_id := Quotient.sound ⟨Q.isoSpanCompIso deflation inflation e.symm hi he⟩

/-- The Q-isomorphism of a reflexive original isomorphism is reflexive. -/
@[simp]
theorem Q.isoOfIso_refl (X : C) (he hi : inflation (𝟙 X)) :
    Q.isoOfIso deflation inflation (Iso.refl X) he hi =
      Iso.refl (Q.of deflation inflation X) := by
  apply Iso.ext
  rfl


end QIsomorphisms

section KGroupMaps

open CategoryTheory.Limits
open scoped ZeroObject

variable [Preadditive C] [HasFiniteBiproducts C]
  [Preadditive D] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D}

/-- Isomorphisms of original-category objects induce isomorphisms of the
Q-category. Both arrows are admissible by the exact-category axioms. -/
def ExactStructure.qIsoOfIso (E : ExactStructure C) {X Y : C} (e : X ≅ Y) :
    Q.of E.deflation E.inflation X ≅ Q.of E.deflation E.inflation Y :=
  Q.isoOfIso E.deflation E.inflation e (E.inflation_of_iso e)
    (E.inflation_of_iso e.symm)

@[simp]
theorem ExactStructure.qIsoOfIso_refl (E : ExactStructure C) (X : C) :
    E.qIsoOfIso (Iso.refl X) = Iso.refl (Q.of E.deflation E.inflation X) := by
  apply Iso.ext
  rfl

/-- A Q-compatible functor with a specified zero-object isomorphism induces
an actual homomorphism between the K-groups based at the chosen zero objects.
The construction uses the explicitly rebased Q-functor. -/
def QCompatibleFunctor.kMapWithZeroIso
    (F : QCompatibleFunctor EC.deflation EC.inflation ED.deflation ED.inflation)
    (e : F.toFunctor.obj (0 : C) ≅ (0 : D)) (n : ℕ) : EC.K n →* ED.K n :=
  pointedShiftedHomotopyGroupMap F.mapQ
    (Q.of EC.deflation EC.inflation (0 : C))
    (Q.of ED.deflation ED.inflation (0 : D)) (ED.qIsoOfIso e) n

end KGroupMaps

end Quillen
