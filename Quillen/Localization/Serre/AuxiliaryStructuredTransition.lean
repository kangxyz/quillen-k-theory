/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.Localization.Serre.AuxiliaryIsoComma
public import Aglib.CategoryTheory.Abelian.SerreClass.Exact

/-! # Actual auxiliary squares for structured Q-transitions -/
@[expose] public section

open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
namespace Quillen.Q
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{u} C] [Abelian C]

/-- The reversed arrow of an ordinary isomorphism is its inverse Q-isomorphism. -/
lemma surjectionArrow_eq_qIsoOfIso_inv {X Y : C} (e : X ≅ Y) :
    surjectionArrow e.hom = ((abelianExactStructure C).qIsoOfIso e).inv := by
  apply mkHom_eq_of_apexIso _ _ _ _ e
  · simp [Q.isoSpan]
  · simp [Q.isoSpan]

/-- The epi version of span naturality uses a cartesian square on right legs. -/
theorem span_naturality_of_surjection_pullback {X Y X' Y' : C}
    (s : AbelianSpan X Y) (t : AbelianSpan X' Y')
    (a : X' ⟶ X) (b : Y' ⟶ Y) (c : t.apex ⟶ s.apex)
    [Epi a] [Epi b]
    (hl : t.l ≫ a = c ≫ s.l) (sq : IsPullback t.r c b s.r) :
    mkHom _ _ s ≫ surjectionArrow b = surjectionArrow a ≫ mkHom _ _ t := by
  let sq₁ : IsPullback t.l (𝟙 t.apex) (𝟙 X') t.l := IsPullback.of_vert_isIso ⟨by simp⟩
  apply mkHom_eq_of_apexIso _ _ _ _ (sq.flip.isoPullback.symm ≪≫ sq₁.isoPullback)
  · change (sq.flip.isoPullback.inv ≫ sq₁.isoPullback.hom) ≫
        pullback.fst (𝟙 X') t.l ≫ a = pullback.fst s.r b ≫ s.l
    simp only [Category.assoc, IsPullback.isoPullback_hom_fst_assoc]
    rw [hl, ← Category.assoc]
    exact congrArg (· ≫ s.l) sq.flip.isoPullback_inv_fst
  · change (sq.flip.isoPullback.inv ≫ sq₁.isoPullback.hom) ≫
        pullback.snd (𝟙 X') t.l ≫ t.r = pullback.snd s.r b ≫ 𝟙 Y'
    simp only [Category.assoc, IsPullback.isoPullback_hom_snd_assoc,
      Category.id_comp, Category.comp_id]
    exact sq.flip.isoPullback_inv_snd

end Quillen.Q
namespace Quillen.SerreLocalization
attribute [local instance] Abelian.hasFiniteBiproducts
attribute [local instance] Quillen.SerreLocalization.canonicalQuotientAbelian
variable {C : Type u} [Category.{u} C] [Abelian C]

/-- The monic pullback counit, retaining the actual ambient Q-arrow. -/
def overBaseChangeForgetInflation {M N : C} (i : M ⟶ N) [Mono i] :
    overBaseChangeQ i ⋙ overForgetQ M ⟶ overForgetQ N where
  app X := Q.inflationArrow (pullback.fst X.obj.of.hom i)
  naturality X Y f := by
    obtain ⟨s, rfl⟩ := Quotient.exists_rep f
    change Q.mkHom _ _ ((overForgetCompatible M).mapSpan ((overBaseChangeCompatible i).mapSpan s)) ≫
        Q.inflationArrow (pullback.fst Y.obj.of.hom i) =
      Q.inflationArrow (pullback.fst X.obj.of.hom i) ≫
        Q.mkHom _ _ ((overForgetCompatible N).mapSpan s)
    apply Q.span_naturality_of_pullback _ _ _ _ (pullback.fst s.apex.hom i)
    · exact overBaseChange_map_isPullback i s.l
    · exact (overBaseChange_map_isPullback i s.r).w

/-- The reversed epimorphic pullback counit is natural on actual Q-spans. -/
def overBaseChangeForgetSurjection {M N : C} (p : M ⟶ N) [Epi p] :
    overForgetQ N ⟶ overBaseChangeQ p ⋙ overForgetQ M where
  app X := Q.surjectionArrow (pullback.fst X.obj.of.hom p)
  naturality X Y f := by
    obtain ⟨s, rfl⟩ := Quotient.exists_rep f
    change Q.mkHom _ _ ((overForgetCompatible N).mapSpan s) ≫
        Q.surjectionArrow (pullback.fst Y.obj.of.hom p) =
      Q.surjectionArrow (pullback.fst X.obj.of.hom p) ≫
        Q.mkHom _ _ ((overForgetCompatible M).mapSpan ((overBaseChangeCompatible p).mapSpan s))
    apply Q.span_naturality_of_surjection_pullback _ _ _ _ (pullback.fst s.apex.hom p)
    · exact (overBaseChange_map_isPullback p s.l).w
    · exact overBaseChange_map_isPullback p s.r

variable (P : ObjectProperty C) [P.IsSerreClass]

/-- The original comparator agrees with the specified-base version at the identity. -/
lemma auxiliaryToIsoStructured_eq_withBaseRefl (N : C) :
    auxiliaryToIsoStructured P N =
      auxiliaryToIsoStructuredWithBase P (Iso.refl (P.isoModSerre.Q.obj N)) := by
  have he (X : AuxiliaryKernel P N) :
      auxiliaryQuotientObjIso P X = auxiliaryQuotientObjIsoWithBase P (Iso.refl _) X := by
    unfold auxiliaryQuotientObjIso auxiliaryQuotientObjIsoWithBase
    congr 1
    ext
    simp
  refine CategoryTheory.Functor.ext (fun X => ?_) ?_
  · apply ObjectProperty.FullSubcategory.ext
    exact congrArg (fun e => StructuredArrow.mk (Y := (auxiliaryForgetQ P N).obj X) e.inv) (he X)
  · intro X Y f
    apply ObjectProperty.hom_ext
    apply StructuredArrow.hom_ext
    simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.eqToHom_hom,
      StructuredArrow.comp_right, StructuredArrow.eqToHom_right]
    change (auxiliaryForgetQ P N).map f = 𝟙 _ ≫ (auxiliaryForgetQ P N).map f ≫ 𝟙 _
    simp

/-- The pullback comparison satisfies the precise comma equation for an inflation. -/
lemma auxiliaryBaseChange_inflation_square {M N : C} (i : M ⟶ N) [Mono i]
    (X : AuxiliaryKernel P N) :
    (auxiliaryQuotientObjIso P ((auxiliaryBaseChange P i).obj X)).inv ≫
        (quotientMapQ P).map (Q.inflationArrow (pullback.fst X.obj.obj.of.hom i)) =
      (quotientMapQ P).map (Q.inflationArrow i) ≫ (auxiliaryQuotientObjIso P X).inv := by
  have : IsIso (P.isoModSerre.Q.map (pullback.snd X.obj.obj.of.hom i)) :=
    auxiliary_quotient_structure_isIso P ((auxiliaryBaseChange P i).obj X)
  apply (cancel_epi (auxiliaryQuotientObjIso P ((auxiliaryBaseChange P i).obj X)).hom).1
  apply (cancel_mono (auxiliaryQuotientObjIso P X).hom).1
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]
  change ((CategoryTheory.ExactCategory.ExactFunctor.serreLocalization P
    P.isoModSerre.Q)).mapQ.map (Q.inflationArrow (pullback.fst X.obj.obj.of.hom i)) ≫
      Q.inflationArrow (P.isoModSerre.Q.map X.obj.obj.of.hom) =
    Q.inflationArrow (P.isoModSerre.Q.map (pullback.snd X.obj.obj.of.hom i)) ≫
      ((CategoryTheory.ExactCategory.ExactFunctor.serreLocalization P P.isoModSerre.Q)).mapQ.map
        (Q.inflationArrow i)
  rw [Q.mapQ_inflationArrow, Q.mapQ_inflationArrow,
    Q.inflationArrow_comp, Q.inflationArrow_comp]
  congr 1
  change P.isoModSerre.Q.map (pullback.fst X.obj.obj.of.hom i) ≫
      P.isoModSerre.Q.map X.obj.obj.of.hom =
    P.isoModSerre.Q.map (pullback.snd X.obj.obj.of.hom i) ≫ P.isoModSerre.Q.map i
  rw [← Functor.map_comp, ← Functor.map_comp, pullback.condition]

/-- The monomorphic base-change square is an actual natural transformation. -/
def auxiliaryStructuredInflationSquare {M N : C} (i : M ⟶ N) [Mono i] :
    auxiliaryBaseChange P i ⋙ auxiliaryToIsoStructured P M ⋙ isoStructuredInclusion P _ ⟶
      auxiliaryToIsoStructured P N ⋙ isoStructuredInclusion P _ ⋙
        StructuredArrow.map ((quotientMapQ P).map (Q.inflationArrow i)) where
  app X := StructuredArrow.homMk (Q.inflationArrow (pullback.fst X.obj.obj.of.hom i))
    (auxiliaryBaseChange_inflation_square P i X)
  naturality X Y f := by
    apply StructuredArrow.hom_ext
    exact (overBaseChangeForgetInflation i).naturality f.hom

/-- An auxiliary quotient identification is the reversal of its ordinary structure map. -/
lemma auxiliaryQuotientObjIso_inv_eq_surjection {N : C} (X : AuxiliaryKernel P N) :
    (auxiliaryQuotientObjIso P X).inv =
      Q.surjectionArrow (P.isoModSerre.Q.map X.obj.obj.of.hom) :=
  (Q.surjectionArrow_eq_qIsoOfIso_inv (asIso (P.isoModSerre.Q.map X.obj.obj.of.hom))).symm

/-- The reversed pullback counit satisfies the precise comma equation for an epi. -/
lemma auxiliaryBaseChange_surjection_square {M N : C} (p : M ⟶ N) [Epi p]
    (X : AuxiliaryKernel P N) :
    (auxiliaryQuotientObjIso P X).inv ≫
        (quotientMapQ P).map (Q.surjectionArrow (pullback.fst X.obj.obj.of.hom p)) =
      (quotientMapQ P).map (Q.surjectionArrow p) ≫
        (auxiliaryQuotientObjIso P ((auxiliaryBaseChange P p).obj X)).inv := by
  have : IsIso (P.isoModSerre.Q.map (pullback.snd X.obj.obj.of.hom p)) :=
    auxiliary_quotient_structure_isIso P ((auxiliaryBaseChange P p).obj X)
  rw [auxiliaryQuotientObjIso_inv_eq_surjection,
    auxiliaryQuotientObjIso_inv_eq_surjection]
  change Q.surjectionArrow (P.isoModSerre.Q.map X.obj.obj.of.hom) ≫
      ((CategoryTheory.ExactCategory.ExactFunctor.serreLocalization P P.isoModSerre.Q)).mapQ.map
        (Q.surjectionArrow (pullback.fst X.obj.obj.of.hom p)) =
    ((CategoryTheory.ExactCategory.ExactFunctor.serreLocalization P P.isoModSerre.Q)).mapQ.map
      (Q.surjectionArrow p) ≫
      Q.surjectionArrow (P.isoModSerre.Q.map (pullback.snd X.obj.obj.of.hom p))
  rw [Q.mapQ_surjectionArrow, Q.mapQ_surjectionArrow,
    Q.surjectionArrow_comp, Q.surjectionArrow_comp]
  congr 1
  change P.isoModSerre.Q.map (pullback.fst X.obj.obj.of.hom p) ≫
      P.isoModSerre.Q.map X.obj.obj.of.hom =
    P.isoModSerre.Q.map (pullback.snd X.obj.obj.of.hom p) ≫ P.isoModSerre.Q.map p
  rw [← Functor.map_comp, ← Functor.map_comp, pullback.condition]

/-- The epimorphic base-change square uses the reversed ordinary counit. -/
def auxiliaryStructuredSurjectionSquare {M N : C} (p : M ⟶ N) [Epi p] :
    auxiliaryToIsoStructured P N ⋙ isoStructuredInclusion P _ ⟶
      auxiliaryBaseChange P p ⋙ auxiliaryToIsoStructured P M ⋙ isoStructuredInclusion P _ ⋙
        StructuredArrow.map ((quotientMapQ P).map (Q.surjectionArrow p)) where
  app X := StructuredArrow.homMk (Q.surjectionArrow (pullback.fst X.obj.obj.of.hom p))
    (auxiliaryBaseChange_surjection_square P p X)
  naturality X Y f := by
    apply StructuredArrow.hom_ext
    exact (overBaseChangeForgetSurjection p).naturality f.hom

end Quillen.SerreLocalization
