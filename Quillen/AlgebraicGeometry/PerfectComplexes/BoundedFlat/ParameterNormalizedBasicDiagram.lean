/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterNormalizedRowForget
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliaryNormalizedRowLocalization
public import Quillen.KTheory.Bass.SchemeModelRowNormalizedInputComposition

/-!
# The original basic localization objects in the normalized row

The middle and open objects are the actual ambient Models. The source uses the
original support on the displayed open immersion. Empty-support comparison is
performed by the original Model forget map, with the explicit open-set equality
casts retained. The whole prescribed auxiliary null keeps its original time.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.LoopPrespectrum Quillen.KTheory.Bass Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace Quillen.PerfectComplexes.ParameterNormalizedBasicLocalization
open GlobalSectionChangeIndex ParameterAuxiliarySupport
open ParameterLaurentTrack ParameterLaurentUnit

/-- The original fixed-factor product pullback acts on the ambient normalized presentation. -/
def restriction {P Q : Scheme.{u}} (f : P ⟶ Q) (X : Scheme.{u}ᵒᵖ) :
    ParameterTensorNormalizedRowPresentation.ambient Q X ⟶
      ParameterTensorNormalizedRowPresentation.ambient P X :=
  SchemeModelRowSeed.normalizedInputMap
    (ParameterModels.ambient Q) (ambientUnit Q) (ambientUnit_naturality Q)
    (ParameterModels.ambient P) (ambientUnit P) (ambientUnit_naturality P)
    (ambientMap f) (ambientUnit_factor f) X

variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)

/-- Original enlargement followed by actual normalized forgetting is the same original forget map.
-/
theorem enlargement_forget (X : Scheme.{u}ᵒᵖ) :
    normalizedPresentationEnlargement f T X ≫
        ParameterTensorNormalizedRowPresentation.forget T.ι X =
      ParameterTensorNormalizedRowPresentation.forget (unionOpen f T).ι X := by
  exact SchemeModelRowSeed.normalizedInputMap_comp_eq
    (fiber f T) (supportedUnit (unionOpen f T).ι)
    (supportedUnit_naturality (unionOpen f T).ι)
    (ambient T) (supportedUnit T.ι) (supportedUnit_naturality T.ι)
    (ParameterModels.ambient Q) (ambientUnit Q) (ambientUnit_naturality Q)
    (ParameterAuxiliarySupport.enlargement f T) (supportedMap_unit (enlargementPair f T))
    (ParameterModels.forget T.ι) (forget_unit T.ι)
    (fun Y => by rw [ParameterAuxiliarySupport.enlargement_forget]; exact forget_unit _ Y)
    (ParameterModels.forget (unionOpen f T).ι) (forget_unit (unionOpen f T).ι)
    (ParameterAuxiliarySupport.enlargement_forget f T) X

omit [IsOpenImmersion f] in
/-- The actual restriction square retains both original support-forget maps. -/
theorem restriction_forget (X : Scheme.{u}ᵒᵖ) :
    normalizedPresentationRestriction f T X ≫
        ParameterTensorNormalizedRowPresentation.forget (inverseOpen f T).ι X =
      ParameterTensorNormalizedRowPresentation.forget T.ι X ≫ restriction f X := by
  let hρ : ∀ Y, Quillen.FunctorIdentityAutomorphism.Preserves
      ((ParameterModels.forget T.ι ≫ ambientMap f).app (laurent.op.obj Y)).functor
      (supportedUnit T.ι Y) (ambientUnit P Y) :=
    fun Y => SchemeModelRowSeed.inputPreserves_comp
      (ambient T) (supportedUnit T.ι) (ParameterModels.ambient Q) (ambientUnit Q)
      (ParameterModels.ambient P) (ambientUnit P)
      (ParameterModels.forget T.ι) (forget_unit T.ι) (ambientMap f) (ambientUnit_factor f) Y
  have hleft := SchemeModelRowSeed.normalizedInputMap_comp_eq
    (ambient T) (supportedUnit T.ι) (supportedUnit_naturality T.ι)
    (openModel f T) (supportedUnit (inverseOpen f T).ι)
    (supportedUnit_naturality (inverseOpen f T).ι)
    (ParameterModels.ambient P) (ambientUnit P) (ambientUnit_naturality P)
    (ParameterAuxiliarySupport.restriction f T)
    (supportedMap_unit (supportRestrictionPair f T))
    (ParameterModels.forget (inverseOpen f T).ι) (forget_unit (inverseOpen f T).ι)
    (fun Y => by rw [ParameterAuxiliarySupport.restriction_forget]; exact hρ Y)
    (ParameterModels.forget T.ι ≫ ambientMap f) hρ
    (ParameterAuxiliarySupport.restriction_forget f T) X
  have hright := SchemeModelRowSeed.normalizedInputMap_comp
    (ambient T) (supportedUnit T.ι) (supportedUnit_naturality T.ι)
    (ParameterModels.ambient Q) (ambientUnit Q) (ambientUnit_naturality Q)
    (ParameterModels.ambient P) (ambientUnit P) (ambientUnit_naturality P)
    (ParameterModels.forget T.ι) (forget_unit T.ι) (ambientMap f) (ambientUnit_factor f) hρ X
  exact hleft.trans hright.symm

/-- Forgetting the auxiliary support retains the entire prescribed null time. -/
def forgottenNull (X : Scheme.{u}ᵒᵖ) :
    Homotopy
      (ParameterTensorNormalizedRowPresentation.forget (unionOpen f T).ι X ≫ restriction f X)
      (zeroHom (normalizedFiberPresentation f T X)
        (ParameterTensorNormalizedRowPresentation.ambient P X)) :=
  ((normalizedPresentationNull f T X).postcomp
    (ParameterTensorNormalizedRowPresentation.forget (inverseOpen f T).ι X)).cast
    (by rw [Category.assoc, restriction_forget, ← Category.assoc, enlargement_forget])
    (by
      apply Hom.ext
      funext n
      ext x
      exact (ParameterTensorNormalizedRowPresentation.forget (inverseOpen f T).ι X).map_point n)

/-- Endpoint casts leave every value of the original postcomposed null unchanged. -/
theorem forgottenNull_level (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (x : (normalizedFiberPresentation f T X).space n) :
    (forgottenNull f T X).level n (r, x) =
      (ParameterTensorNormalizedRowPresentation.forget (inverseOpen f T).ι X).map n
        ((normalizedPresentationNull f T X).level n (r, x)) := rfl

/-- The auxiliary union for the original open inclusion is precisely the original open. -/
theorem basic_union_eq (Q : Scheme.{u}) (U : Q.Opens) :
    unionOpen U.ι ⊥ = U := by
  simp only [unionOpen, bot_sup_eq, Scheme.Opens.opensRange_ι]

/-- The original inverse image of the bottom open is the bottom open. -/
theorem inverseOpen_bottom {P Q : Scheme.{u}} (f : P ⟶ Q) :
    inverseOpen f ⊥ = ⊥ := by
  simp only [inverseOpen, Scheme.Hom.preimage_bot]

/-- This explicit object cast retains the displayed original supported source. -/
def basicSourceIso (Q : Scheme.{u}) (U : Q.Opens) (X : Scheme.{u}ᵒᵖ) :
    normalizedFiberPresentation U.ι ⊥ X ≅
      ParameterTensorNormalizedRowPresentation.supported U.ι X :=
  eqToIso (congrArg
    (fun V : Q.Opens => ParameterTensorNormalizedRowPresentation.supported V.ι X)
    (basic_union_eq Q U))

private theorem forget_open_eq (Q : Scheme.{u}) {U V : Q.Opens} (h : U = V)
    (X : Scheme.{u}ᵒᵖ) :
    (eqToIso (congrArg
      (fun W : Q.Opens => ParameterTensorNormalizedRowPresentation.supported W.ι X) h)).hom ≫
        ParameterTensorNormalizedRowPresentation.forget V.ι X =
      ParameterTensorNormalizedRowPresentation.forget U.ι X := by
  subst V
  simp only [eqToIso_refl, Iso.refl_hom, Category.id_comp]

/-- The explicit source cast retains the actual original supported-forget arrow. -/
theorem basicSourceIso_forget (Q : Scheme.{u}) (U : Q.Opens) (X : Scheme.{u}ᵒᵖ) :
    (basicSourceIso Q U X).hom ≫ ParameterTensorNormalizedRowPresentation.forget U.ι X =
      ParameterTensorNormalizedRowPresentation.forget (unionOpen U.ι ⊥).ι X :=
  forget_open_eq Q (basic_union_eq Q U) X

/-- The basic null is the prescribed auxiliary null with actual forget and source-cast maps. -/
def basicNull (Q : Scheme.{u}) (U : Q.Opens) (X : Scheme.{u}ᵒᵖ) :
    Homotopy (ParameterTensorNormalizedRowPresentation.forget U.ι X ≫ restriction U.ι X)
      (zeroHom (ParameterTensorNormalizedRowPresentation.supported U.ι X)
        (ParameterTensorNormalizedRowPresentation.ambient U.toScheme X)) :=
  ((forgottenNull U.ι ⊥ X).precomp (basicSourceIso Q U X).inv).cast
    (by
      rw [← basicSourceIso_forget Q U X]
      simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp])
    (by apply Hom.ext; funext n; ext x; rfl)

private theorem iso_precomp_level {E E' F : Quillen.LoopPrespectrum.{u}}
    (e : E ≅ E') {f g : E ⟶ F} {f' g' : E' ⟶ F} (H : Homotopy f g)
    (hf : e.inv ≫ f = f') (hg : e.inv ≫ g = g')
    (n : ℕ) (r : unitInterval) (x : E.space n) :
    H.level n (r, x) = ((H.precomp e.inv).cast hf hg).level n (r, e.hom.map n x) := by
  have h := congrArg (fun k => k.map n x) e.hom_inv_id
  change e.inv.map n (e.hom.map n x) = x at h
  change H.level n (r, x) = H.level n (r, e.inv.map n (e.hom.map n x))
  rw [h]

/-- The source cast and target forgetting keep the original null time pointwise. -/
theorem basicNull_comparison (Q : Scheme.{u}) (U : Q.Opens) (X : Scheme.{u}ᵒᵖ)
    (n : ℕ) (r : unitInterval) (x : (normalizedFiberPresentation U.ι ⊥ X).space n) :
    (ParameterTensorNormalizedRowPresentation.forget (inverseOpen U.ι ⊥).ι X).map n
        ((normalizedPresentationNull U.ι ⊥ X).level n (r, x)) =
      (basicNull Q U X).level n (r, (basicSourceIso Q U X).hom.map n x) := by
  exact (forgottenNull_level U.ι ⊥ X n r x).symm.trans
    (iso_precomp_level (basicSourceIso Q U X) (forgottenNull U.ι ⊥ X) _ _ n r x)

end Quillen.PerfectComplexes.ParameterNormalizedBasicLocalization
