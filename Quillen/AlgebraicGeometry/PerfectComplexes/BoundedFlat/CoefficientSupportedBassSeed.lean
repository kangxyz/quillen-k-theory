/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportLocalizationModels
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientOpenBassSeed
public import Quillen.Waldhausen.SConstruction.Iterated.DiagramNullIdentityAction

/-!
# Original supported and ambient global Bass seeds and whole-null compatibility

The actual forward Laurent unit restricts through the original supported inclusion.
Its coefficient equation gives the original supported seed; the unchanged ambient
seed and existing coarse seed preserve both original arrows. The actual reversed
zero-to-inclusion null interchanges with these units at independent scalar and null
parameters, so every original null time slice satisfies the same strict seed square.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.PolynomialBaseChange
open Quillen.KTheory.Bass Quillen.FunctorIdentityAutomorphism
open AlgebraicGeometry.Scheme.PolynomialLaurent AlgebraicGeometry.Scheme.CoefficientBaseChange
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]
attribute [local irreducible] boundedFlatCoefficientOriginalEvaluation
  boundedFlatPerfectGlobalUnitIso boundedFlatCoefficientSectionLaurentUnitIso

/-- The original joint section unit restricted through the actual supported inclusion. -/
def boundedFlatCoefficientSupportedUnitIso (a : Under R) (r : (Γ(Spec a.right, ⊤))ˣ) :
    𝟭 (BoundedFlatCoefficientSupportSections f a) ≅ 𝟭 (BoundedFlatCoefficientSupportSections f a) :=
  lift (boundedFlatCoefficientSectionSupported (schemeMap f a)).ι
    (boundedFlatCoefficientSectionUnitIso (op Q, a) (boundedFlatCoefficientUnit (op Q, a) r))

/-- Forgetting support keeps precisely the original forward unit component. -/
theorem boundedFlatCoefficientSupportedUnitIso_hom
    (a : Under R) (r : (Γ(Spec a.right, ⊤))ˣ) (S : BoundedFlatCoefficientSupportSections f a) :
    ((boundedFlatCoefficientSupportedUnitIso f a r).hom.app S).hom =
      (boundedFlatCoefficientSectionUnitIso (op Q, a)
        (boundedFlatCoefficientUnit (op Q, a) r)).hom.app S.obj :=
  map_lift_hom (boundedFlatCoefficientSectionSupported (schemeMap f a)).ι _ S

/-- The actual forward Laurent coordinate on the original supported coefficient fiber. -/
def boundedFlatCoefficientSupportedLaurentUnitIso (a : Under R) :=
  boundedFlatCoefficientSupportedUnitIso f ((laurentUnderFunctor R).obj a)
    (laurentGlobalUnit a.right)

/-- Actual supported coefficient reindexing preserves the same native forward Laurent unit. -/
theorem boundedFlatCoefficientSupportedLaurentUnitIso_coefficient
    {a b : Under R} (g : a ⟶ b) :
    Preserves ((boundedFlatCoefficientSupportedModelFunctor f).map
      ((laurentUnderFunctor R).map g)).functor
      (boundedFlatCoefficientSupportedLaurentUnitIso f a)
      (boundedFlatCoefficientSupportedLaurentUnitIso f b) := by
  change Preserves (boundedFlatCoefficientSupportedSectionsMap
    (schemeMap f ((laurentUnderFunctor R).obj a)) (schemeMap f ((laurentUnderFunctor R).obj b))
    (i := (op Q, (laurentUnderFunctor R).obj a))
    (k := (op Q, (laurentUnderFunctor R).obj b))
    (𝟙 (op Q), (laurentUnderFunctor R).map g)
    (boundedFlatCoefficientOpenPairMap f ((laurentUnderFunctor R).map g)).hom.left
    (Arrow.w (boundedFlatCoefficientOpenPairMap f ((laurentUnderFunctor R).map g)).hom)) _ _
  intro S
  apply ObjectProperty.hom_ext
  change (boundedFlatCoefficientSectionsMap
    (i := (op Q, (laurentUnderFunctor R).obj a))
    (k := (op Q, (laurentUnderFunctor R).obj b))
    (𝟙 (op Q), (laurentUnderFunctor R).map g)).map
      ((boundedFlatCoefficientSupportedLaurentUnitIso f a).hom.app S).hom = _
  dsimp only [boundedFlatCoefficientSupportedLaurentUnitIso]
  rw [boundedFlatCoefficientSupportedUnitIso_hom, boundedFlatCoefficientSupportedUnitIso_hom]
  simpa only [boundedFlatCoefficientSectionLaurentUnitIso,
    boundedFlatCoefficientSupportedSectionsMap, ObjectProperty.lift,
    Functor.comp_obj, ObjectProperty.ι_obj, Functor.id_obj] using
      boundedFlatCoefficientSectionLaurentUnitIso_coefficient Q g S.obj

/-- The original forward supported Laurent action with its actual coefficient equation. -/
def boundedFlatCoefficientSupportedLaurentAction :
    LaurentSeed.ModelAction (boundedFlatCoefficientSupportedModelFunctor f) where
  unit := boundedFlatCoefficientSupportedLaurentUnitIso f
  naturality := boundedFlatCoefficientSupportedLaurentUnitIso_coefficient f

/-- The unchanged ambient forward Laurent action on the native fine coefficient row. -/
def boundedFlatCoefficientAmbientLaurentAction (Q : Over (Spec R)) :
    LaurentSeed.ModelAction (boundedFlatCoefficientSectionModelRow Q) where
  unit := boundedFlatCoefficientSectionLaurentUnitIso Q
  naturality := boundedFlatCoefficientSectionLaurentUnitIso_coefficient Q

/-- Construct the supported seed with the original square, source null and concatenation. -/
def boundedFlatCoefficientSupportedBassSeed :
    boundedFlatCoefficientSupportedPrespectrumFunctor f ⟶
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
        (boundedFlatCoefficientSupportedPrespectrumFunctor f) :=
  (boundedFlatCoefficientSupportedLaurentAction f).track.seed

/-- Construct the native fine ambient seed using that same prescribed Bass construction. -/
def boundedFlatCoefficientAmbientBassSeed (Q : Over (Spec R)) :
    boundedFlatCoefficientAmbientPrespectrumFunctor Q ⟶
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
        (boundedFlatCoefficientAmbientPrespectrumFunctor Q) :=
  (boundedFlatCoefficientAmbientLaurentAction Q).track.seed

/-- Original support inclusion preserves the entire supported Laurent-action track. -/
theorem boundedFlatCoefficientSupportedForget_laurent_apply
    (a : Under R) (n : ℕ) (t : unitInterval)
    (x : ((boundedFlatCoefficientSupportedPrespectrumFunctor f).obj a).space n) :
    ((boundedFlatCoefficientSupportedForgetPrespectrumTransformation f).app
      ((laurentUnderFunctor R).obj a)).map n
        (((boundedFlatCoefficientSupportedLaurentAction f).track.homotopy a).level n (t, x)) =
      ((boundedFlatCoefficientAmbientLaurentAction Q).track.homotopy a).level n
        (t, ((boundedFlatCoefficientSupportedForgetPrespectrumTransformation f).app a).map n x) :=
  LaurentSeed.ModelAction.track_square (boundedFlatCoefficientSupportedLaurentAction f)
    (boundedFlatCoefficientAmbientLaurentAction Q)
    (boundedFlatCoefficientSupportedForgetModelTransformation f)
    (fun a S ↦ by
      simpa only [boundedFlatCoefficientSupportedLaurentAction,
        boundedFlatCoefficientAmbientLaurentAction, boundedFlatCoefficientSectionLaurentUnitIso,
        boundedFlatCoefficientSupportedLaurentUnitIso,
        boundedFlatCoefficientSupportedForgetModelTransformation,
        boundedFlatCoefficientSupportedForgetModelMap,
        boundedFlatCoefficientSupportedModelFunctor, boundedFlatCoefficientSupportedModel,
        Functor.id_obj, ObjectProperty.ι_obj, ObjectProperty.ι_map] using
          boundedFlatCoefficientSupportedUnitIso_hom f
            ((laurentUnderFunctor R).obj a) (laurentGlobalUnit a.right) S) a n t x

/-- The actual supported inclusion preserves the unchanged complete Bass seed. -/
theorem boundedFlatCoefficientSupportedBassSeed_forget :
    boundedFlatCoefficientSupportedBassSeed f ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedFlatCoefficientSupportedForgetPrespectrumTransformation f) =
      boundedFlatCoefficientSupportedForgetPrespectrumTransformation f ≫
        boundedFlatCoefficientAmbientBassSeed Q :=
  LaurentSeed.Track.seed_square (boundedFlatCoefficientSupportedLaurentAction f).track
    (boundedFlatCoefficientAmbientLaurentAction Q).track
    (boundedFlatCoefficientSupportedForgetPrespectrumTransformation f)
    (boundedFlatCoefficientSupportedForget_laurent_apply f)

/-- Identity change of weakness keeps the original ambient Laurent-action time unchanged. -/
theorem boundedFlatCoefficientAmbientOpen_laurent_apply
    (a : Under R) (n : ℕ) (t : unitInterval)
    (x : ((boundedFlatCoefficientAmbientPrespectrumFunctor Q).obj a).space n) :
    ((boundedFlatCoefficientAmbientOpenPrespectrumTransformation f).app
      ((laurentUnderFunctor R).obj a)).map n
        (((boundedFlatCoefficientAmbientLaurentAction Q).track.homotopy a).level n (t, x)) =
      ((boundedFlatCoefficientOpenLaurentAction f).track.homotopy a).level n
        (t, ((boundedFlatCoefficientAmbientOpenPrespectrumTransformation f).app a).map n x) :=
  LaurentSeed.ModelAction.track_square (boundedFlatCoefficientAmbientLaurentAction Q)
    (boundedFlatCoefficientOpenLaurentAction f)
    (boundedFlatCoefficientOpenChangeWeakModelTransformation f) (fun _ _ ↦ rfl) a n t x

/-- Original ambient change of weakness preserves its entire Bass seed. -/
theorem boundedFlatCoefficientAmbientBassSeed_open :
    boundedFlatCoefficientAmbientBassSeed Q ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedFlatCoefficientAmbientOpenPrespectrumTransformation f) =
      boundedFlatCoefficientAmbientOpenPrespectrumTransformation f ≫
        boundedFlatCoefficientOpenBassSeed f :=
  LaurentSeed.Track.seed_square (boundedFlatCoefficientAmbientLaurentAction Q).track
    (boundedFlatCoefficientOpenLaurentAction f).track
    (boundedFlatCoefficientAmbientOpenPrespectrumTransformation f)
    (boundedFlatCoefficientAmbientOpen_laurent_apply f)

/-- The same reversed zero-to-inclusion null has genuine whole identity-action compatibility. -/
theorem boundedFlatCoefficientSupportedOpenNull_unitCompatible (a : Under R) :
    ZeroNullUnitCompatible
      ((boundedFlatCoefficientSupportedForgetModelTransformation f).app a)
      ((boundedFlatCoefficientOpenChangeWeakModelTransformation f).app a)
      ((boundedFlatCoefficientSupportedOpenDiagramNull f).homotopy a) :=
  prespectrumCompositeZeroNullHomotopy_unitCompatible
    ((boundedFlatCoefficientSupportedForgetModelTransformation f).app a)
    ((boundedFlatCoefficientOpenChangeWeakModelTransformation f).app a)
    (boundedFlatCoefficientSupportedZeroToOpen f a)
    (boundedFlatCoefficientSupportedZeroToOpen_weak f a)

/-- Actual original support inclusion and weakness change preserve every coefficient unit. -/
theorem boundedFlatCoefficientSupportedOpenNull_unitInterchange
    (a : Under R) (r : (Γ(Spec a.right, ⊤))ˣ) :
    IdentityActionInterchange
      (V := (boundedFlatCoefficientSupportedModelFunctor f).obj a)
      (T := (boundedFlatCoefficientOpenModelFunctor f).obj a)
      ((boundedFlatCoefficientSupportedOpenDiagramNull f).homotopy a)
      (boundedFlatCoefficientSupportedUnitIso f a r)
      (boundedFlatCoefficientSectionUnitIso (op Q, a) (boundedFlatCoefficientUnit (op Q, a) r)) :=
  boundedFlatCoefficientSupportedOpenNull_unitCompatible f a _ _
    (fun S ↦ boundedFlatCoefficientSupportedUnitIso_hom f a r S)

/-- Laurent scalar and supported localization-null times remain independent. -/
theorem boundedFlatCoefficientSupportedOpenNull_laurentInterchange (a : Under R) :
    TrackInterchange
      ((boundedFlatCoefficientSupportedOpenDiagramNull f).homotopy a)
      ((boundedFlatCoefficientSupportedOpenDiagramNull f).homotopy
        ((laurentUnderFunctor R).obj a))
      ((boundedFlatCoefficientSupportedLaurentAction f).track.homotopy a)
      ((boundedFlatCoefficientOpenLaurentAction f).track.homotopy a) :=
  modelDiagramNull_coefficientCompatible
    (r := boundedFlatCoefficientSupportedForgetModelTransformation f)
    (q := boundedFlatCoefficientOpenChangeWeakModelTransformation f)
    (boundedFlatCoefficientSupportedOpenDiagramNull f) ((laurentUnderCoefficient R).app a)
    ((boundedFlatCoefficientSupportedLaurentAction f).unit a)
    ((boundedFlatCoefficientOpenLaurentAction f).unit a)
    (by
      simpa only [boundedFlatCoefficientSupportedLaurentAction,
        boundedFlatCoefficientOpenLaurentAction, boundedFlatCoefficientSectionLaurentUnitIso,
        boundedFlatCoefficientSupportedLaurentUnitIso] using
          boundedFlatCoefficientSupportedOpenNull_unitInterchange f
            ((laurentUnderFunctor R).obj a) (laurentGlobalUnit a.right))

/-- Each time of the same whole supported null gives its original coefficient transformation. -/
def boundedFlatCoefficientSupportedOpenNullTimeSlice (s : unitInterval) :
    boundedFlatCoefficientSupportedPrespectrumFunctor f ⟶
      boundedFlatCoefficientOpenPrespectrumFunctor f :=
  diagramHomotopyAt
    (η := boundedFlatCoefficientSupportedForgetPrespectrumTransformation f ≫
      boundedFlatCoefficientAmbientOpenPrespectrumTransformation f)
    (θ := diagramZeroMap (boundedFlatCoefficientSupportedPrespectrumFunctor f)
      (boundedFlatCoefficientOpenPrespectrumFunctor f))
    (boundedFlatCoefficientSupportedOpenDiagramNull f).homotopy
    (boundedFlatCoefficientSupportedOpenDiagramNull f).naturality s

/-- Every original localization-null time satisfies the actual unchanged strict seed square. -/
theorem boundedFlatCoefficientSupportedOpenNullTimeSlice_seed (s : unitInterval) :
    boundedFlatCoefficientSupportedBassSeed f ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedFlatCoefficientSupportedOpenNullTimeSlice f s) =
      boundedFlatCoefficientSupportedOpenNullTimeSlice f s ≫
        boundedFlatCoefficientOpenBassSeed f :=
  LaurentSeed.Track.seed_square (boundedFlatCoefficientSupportedLaurentAction f).track
    (boundedFlatCoefficientOpenLaurentAction f).track
    (boundedFlatCoefficientSupportedOpenNullTimeSlice f s)
    (fun a n t x ↦ boundedFlatCoefficientSupportedOpenNull_laurentInterchange f a n s t x)

end Quillen.PerfectComplexes
