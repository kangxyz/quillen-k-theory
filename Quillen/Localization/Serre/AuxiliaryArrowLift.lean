/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.Localization.Serre.AuxiliaryIsoComma

/-!
# Common-base lifting of quotient-isomorphism Q-arrows

An ambient Q-arrow that becomes invertible in the quotient has an actual
representative over one ordinary Serre-isomorphic base. Both endpoints
and the arrow lift together, using the ordinary pushout of a span.
-/
@[expose] public section

open CategoryTheory.ExactCategory



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
namespace Quillen.SerreLocalization
attribute [local instance] Abelian.hasFiniteBiproducts quotientAbelian
variable {C : Type u} [Category.{u} C] [Abelian C]
variable (P : ObjectProperty C) [P.IsSerreClass]

/-- Regard an ordinary Serre-isomorphism as an auxiliary object. -/
def auxiliaryOverMk {X N : C} (f : X ⟶ N) (hf : P.isoModSerre f) : AuxiliaryKernel P N :=
  ⟨Q.of _ _ (Over.mk f), hf⟩

/-- Every leg of a span whose quotient Q-arrow is invertible is a
Serre-isomorphism in the original abelian category. -/
theorem span_isoModSerre_of_quotient_isIso {X Y : C} (s : Q.AbelianSpan X Y)
    [IsIso ((quotientMapQ P).map (Q.mkHom _ _ s))] :
    P.isoModSerre s.l ∧ P.isoModSerre s.r := by
  let t : Q.AbelianSpan (P.isoModSerre.Q.obj X) (P.isoModSerre.Q.obj Y) :=
    (quotientExactFunctor P).toQCompatibleFunctor.mapSpan s
  have : IsIso (Q.mkHom _ _ t) := inferInstanceAs
    (IsIso ((quotientMapQ P).map (Q.mkHom _ _ s)))
  obtain ⟨hl, hr⟩ := Q.isIso_legs_of_isIso t
  exact ⟨(ObjectProperty.SerreClassLocalization.isIso_map_iff P.isoModSerre.Q P s.l).1 hl,
    (ObjectProperty.SerreClassLocalization.isIso_map_iff P.isoModSerre.Q P s.r).1 hr⟩

/-- The pushout span is genuinely a span over its common target. -/
def spanOverPushout {X Y : C} (s : Q.AbelianSpan X Y) :
    Span (overDeflation (pushout s.l s.r)) (overInflation (pushout s.l s.r))
      (Over.mk (pushout.inl s.l s.r)) (Over.mk (pushout.inr s.l s.r)) where
  apex := Over.mk (s.l ≫ pushout.inl s.l s.r)
  l := Over.homMk s.l rfl
  r := Over.homMk s.r pushout.condition.symm
  wl := inferInstanceAs (Epi s.l)
  wr := inferInstanceAs (Mono s.r)

/-- The lifted ordinary span retains exactly the original ambient Q-arrow. -/
@[simp]
lemma spanOverPushout_forget {X Y : C} (s : Q.AbelianSpan X Y) :
    (overForgetQ (pushout s.l s.r)).map (Q.mkHom _ _ (spanOverPushout s)) =
      Q.mkHom _ _ s := rfl

/-- A quotient-isomorphism span supplies auxiliary objects at both cospan endpoints. -/
def auxiliarySpanLift {X Y : C} (s : Q.AbelianSpan X Y)
    (hl : P.isoModSerre s.l) (hr : P.isoModSerre s.r) :
    auxiliaryOverMk P (pushout.inl s.l s.r) (MorphismProperty.pushout_inl _ _ hr) ⟶
      auxiliaryOverMk P (pushout.inr s.l s.r) (MorphismProperty.pushout_inr _ _ hl) :=
  ObjectProperty.homMk (Q.mkHom _ _ (spanOverPushout s))

@[simp]
lemma auxiliarySpanLift_forget {X Y : C} (s : Q.AbelianSpan X Y)
    (hl : P.isoModSerre s.l) (hr : P.isoModSerre s.r) :
    (auxiliaryForgetQ P (pushout s.l s.r)).map (auxiliarySpanLift P s hl hr) =
      Q.mkHom _ _ s := rfl

/-- Every ambient Q-arrow inverted by the quotient lifts together with its
endpoints over one ordinary base. No ordinary lift between the fixed endpoints
is assumed. -/
theorem exists_auxiliary_arrow_lift {X Y : C}
    (f : Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation X ⟶ Q.of _ _
      Y)
    [IsIso ((quotientMapQ P).map f)] :
    ∃ (N : C) (i : X ⟶ N) (p : Y ⟶ N) (hi : P.isoModSerre i) (hp : P.isoModSerre p)
      (_ : Mono i) (_ : Epi p)
      (g : auxiliaryOverMk P i hi ⟶ auxiliaryOverMk P p hp),
      (auxiliaryForgetQ P N).map g = f := by
  obtain ⟨s, hs⟩ := Quotient.exists_rep f
  have : IsIso ((quotientMapQ P).map (Q.mkHom _ _ s)) := by
    rw [show Q.mkHom _ _ s = f from hs]
    infer_instance
  obtain ⟨hl, hr⟩ := span_isoModSerre_of_quotient_isIso P s
  exact ⟨pushout s.l s.r, pushout.inl s.l s.r, pushout.inr s.l s.r,
    MorphismProperty.pushout_inl _ _ hr, MorphismProperty.pushout_inr _ _ hl,
    inferInstance, inferInstance, auxiliarySpanLift P s hl hr, hs⟩

/-- The ordinary quotient isomorphism underlying a structured Q-isomorphism. -/
def isoStructuredOrdinaryIso {V : Quotient P}
    (A : IsoStructuredComma P (Q.of (quotientExactStructure P).deflation
      (quotientExactStructure P).inflation V)) :
    V ≅ P.isoModSerre.Q.obj A.obj.right.obj.of :=
  (Q.exists_iso_of_isIso (hf := A.property) A.obj.hom).choose

lemma isoStructuredOrdinaryIso_hom {V : Quotient P}
    (A : IsoStructuredComma P (Q.of (quotientExactStructure P).deflation
      (quotientExactStructure P).inflation V)) :
    ((quotientExactStructure P).qIsoOfIso (isoStructuredOrdinaryIso P A)).hom = A.obj.hom :=
  (Q.exists_iso_of_isIso (hf := A.property) A.obj.hom).choose_spec

/-- A Serre-isomorphic map from the source of a structured object determines
an ordinary quotient identification of its new base. -/
def auxiliaryArrowLiftBaseIso {V : Quotient P}
    (A : IsoStructuredComma P (Q.of (quotientExactStructure P).deflation
      (quotientExactStructure P).inflation V)) {N : C}
    (i : A.obj.right.obj.of ⟶ N) (hi : P.isoModSerre i) : P.isoModSerre.Q.obj N ≅ V := by
  have : IsIso (P.isoModSerre.Q.map i) := Localization.inverts _ _ _ hi
  exact (asIso (P.isoModSerre.Q.map i)).symm ≪≫ (isoStructuredOrdinaryIso P A).symm

/-- This chosen base identification lifts the source object exactly. -/
theorem auxiliaryArrowLiftBaseIso_obj {V : Quotient P}
    (A : IsoStructuredComma P (Q.of (quotientExactStructure P).deflation
      (quotientExactStructure P).inflation V)) {N : C}
    (i : A.obj.right.obj.of ⟶ N) (hi : P.isoModSerre i) :
    (auxiliaryToIsoStructuredWithBase P (auxiliaryArrowLiftBaseIso P A i hi)).obj
      (auxiliaryOverMk P i hi) = A := by
  apply ObjectProperty.FullSubcategory.ext
  refine StructuredArrow.obj_ext _ A.obj (by rfl) ?_
  change (auxiliaryQuotientObjIsoWithBase P (auxiliaryArrowLiftBaseIso P A i hi)
    (auxiliaryOverMk P i hi)).inv ≫ (quotientMapQ P).map (𝟙 A.obj.right) = A.obj.hom
  erw [(quotientMapQ P).map_id, Category.comp_id]
  have : IsIso (P.isoModSerre.Q.map i) := Localization.inverts _ _ _ hi
  have he : asIso (P.isoModSerre.Q.map i) ≪≫ auxiliaryArrowLiftBaseIso P A i hi =
      (isoStructuredOrdinaryIso P A).symm := by simp [auxiliaryArrowLiftBaseIso]
  change ((quotientExactStructure P).qIsoOfIso
    (asIso (P.isoModSerre.Q.map i) ≪≫ auxiliaryArrowLiftBaseIso P A i hi)).inv = A.obj.hom
  rw [he]
  exact isoStructuredOrdinaryIso_hom P A

/-- Every single arrow in the quotient isomorphism comma lifts, with both
endpoints and its exact triangle, to one ordinary auxiliary category. -/
theorem exists_isoStructured_arrow_lift {V : Quotient P}
    {A B : IsoStructuredComma P (Q.of (quotientExactStructure P).deflation
      (quotientExactStructure P).inflation V)} (f : A ⟶ B) :
    ∃ (N : C) (φ : P.isoModSerre.Q.obj N ≅ V) (X Y : AuxiliaryKernel P N) (g : X ⟶ Y)
      (hX : (auxiliaryToIsoStructuredWithBase P φ).obj X = A)
      (hY : (auxiliaryToIsoStructuredWithBase P φ).obj Y = B),
      (auxiliaryToIsoStructuredWithBase P φ).map g ≫ eqToHom hY = eqToHom hX ≫ f := by
  have : IsIso (A.obj.hom ≫ (quotientMapQ P).map f.hom.right) := by
    rw [StructuredArrow.w f.hom]
    infer_instance
  have : IsIso ((quotientMapQ P).map f.hom.right) :=
    IsIso.of_isIso_comp_left A.obj.hom _
  obtain ⟨N, i, p, hi, hp, _, _, g, hg⟩ := exists_auxiliary_arrow_lift P f.hom.right
  let φ := auxiliaryArrowLiftBaseIso P A i hi
  let X := auxiliaryOverMk P i hi
  let Y := auxiliaryOverMk P p hp
  let F := auxiliaryToIsoStructuredWithBase P φ
  have hX : F.obj X = A := auxiliaryArrowLiftBaseIso_obj P A i hi
  have hY : F.obj Y = B := by
    apply ObjectProperty.FullSubcategory.ext
    refine StructuredArrow.obj_ext _ B.obj (by rfl) ?_
    change (F.obj Y).obj.hom ≫ (quotientMapQ P).map (𝟙 B.obj.right) = B.obj.hom
    erw [(quotientMapQ P).map_id, Category.comp_id]
    have hFg := StructuredArrow.w (F.map g).hom
    have hXh : (F.obj X).obj.hom = A.obj.hom := by
      have hh := StructuredArrow.w (eqToHom hX).hom
      simp only [ObjectProperty.eqToHom_hom, StructuredArrow.eqToHom_right,
        eqToHom_refl] at hh
      erw [(quotientMapQ P).map_id, Category.comp_id] at hh
      exact hh
    change (F.obj X).obj.hom ≫ (quotientMapQ P).map ((auxiliaryForgetQ P N).map g) =
      (F.obj Y).obj.hom at hFg
    rw [hg, hXh, StructuredArrow.w f.hom] at hFg
    exact hFg.symm
  refine ⟨N, φ, X, Y, g, hX, hY, ?_⟩
  apply ObjectProperty.hom_ext
  apply StructuredArrow.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.eqToHom_hom,
    StructuredArrow.comp_right, StructuredArrow.eqToHom_right]
  change (auxiliaryForgetQ P N).map g ≫ 𝟙 _ = 𝟙 _ ≫ f.hom.right
  simpa using hg

end Quillen.SerreLocalization
