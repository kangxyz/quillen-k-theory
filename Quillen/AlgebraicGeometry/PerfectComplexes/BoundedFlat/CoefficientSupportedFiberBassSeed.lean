/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedFiberLocalizationModels
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedOpenBassSeed
public import Quillen.Waldhausen.SConstruction.Iterated.DiagramNullIdentityAction

/-!
# Original auxiliary intersection-support and ambient Bass seeds

The actual forward Laurent unit restricts through the original union-support
fiber and its literal inclusion into auxiliary ambient support. Original
coefficient and unit equations construct both seeds. Identity weakness change
preserves the same ambient unit, and the canonical native whole support null
interchanges with the original units at independent scalar and null times.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open Quillen.KTheory.Bass Quillen.FunctorIdentityAutomorphism
open AlgebraicGeometry.Scheme.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)
attribute [local irreducible] boundedFlatCoefficientOriginalEvaluation
  boundedFlatPerfectGlobalUnitIso boundedFlatCoefficientSectionLaurentUnitIso

/-- The original forward Laurent unit on the actual intersection-support native fiber. -/
def boundedFlatCoefficientSupportedFiberLaurentUnitIso (a : Under R) :=
  lift (boundedFlatCoefficientSectionSupported
    (boundedFlatCoefficientFiberSupportOpen f T ((laurentUnderFunctor R).obj a)).ι).ι
    (boundedFlatCoefficientSectionLaurentUnitIso Q a)

private theorem fiberMap_preserves_lift {i k : Index R} {U V : Scheme.{u}}
    (j : U ⟶ space i) (j' : V ⟶ space k) [IsOpenImmersion j] [IsOpenImmersion j']
    (η : i ⟶ k) (l : V ⟶ U) (h : l ≫ j = j' ≫ AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
      η)
    (α : 𝟭 (BoundedFlatCoefficientSections i) ≅ 𝟭 (BoundedFlatCoefficientSections i))
    (β : 𝟭 (BoundedFlatCoefficientSections k) ≅ 𝟭 (BoundedFlatCoefficientSections k))
    (hαβ : Preserves (boundedFlatCoefficientSectionsMap η) α β) :
    Preserves (boundedFlatCoefficientSupportedSectionsMap j j' η l h)
      (lift (boundedFlatCoefficientSectionSupported j).ι α)
      (lift (boundedFlatCoefficientSectionSupported j').ι β) := by
  intro S
  apply ObjectProperty.hom_ext
  change (boundedFlatCoefficientSectionsMap η).map
    ((lift (boundedFlatCoefficientSectionSupported j).ι α).hom.app S).hom =
    ((lift (boundedFlatCoefficientSectionSupported j').ι β).hom.app
      ((boundedFlatCoefficientSupportedSectionsMap j j' η l h).obj S)).hom
  rw [show ((lift (boundedFlatCoefficientSectionSupported j).ι α).hom.app S).hom =
    α.hom.app S.obj from map_lift_hom (boundedFlatCoefficientSectionSupported j).ι α S,
    show ((lift (boundedFlatCoefficientSectionSupported j').ι β).hom.app
      ((boundedFlatCoefficientSupportedSectionsMap j j' η l h).obj S)).hom =
      β.hom.app ((boundedFlatCoefficientSectionsMap η).obj S.obj) from
      map_lift_hom (boundedFlatCoefficientSectionSupported j').ι β _]
  exact hαβ S.obj

/-- Actual coefficient reindexing preserves every original forward fiber-unit component. -/
theorem boundedFlatCoefficientSupportedFiberLaurentUnitIso_coefficient
    {a b : Under R} (g : a ⟶ b) :
    Preserves ((boundedFlatCoefficientSupportedFiberModelFunctor f T).map
      ((laurentUnderFunctor R).map g)).functor
      (boundedFlatCoefficientSupportedFiberLaurentUnitIso f T a)
      (boundedFlatCoefficientSupportedFiberLaurentUnitIso f T b) :=
  fiberMap_preserves_lift
    (boundedFlatCoefficientFiberSupportOpen f T ((laurentUnderFunctor R).obj a)).ι
    (boundedFlatCoefficientFiberSupportOpen f T ((laurentUnderFunctor R).obj b)).ι
    (𝟙 (op Q), (laurentUnderFunctor R).map g)
    (boundedFlatCoefficientFiberSupportPairMap f T ((laurentUnderFunctor R).map g)).hom.left
    (Arrow.w (boundedFlatCoefficientFiberSupportPairMap f T ((laurentUnderFunctor R).map g)).hom)
    _ _ (boundedFlatCoefficientSectionLaurentUnitIso_coefficient Q g)

/-- The original actual fiber action with its proved coefficient equation. -/
def boundedFlatCoefficientSupportedFiberLaurentAction :
    LaurentSeed.ModelAction (boundedFlatCoefficientSupportedFiberModelFunctor f T) where
  unit := boundedFlatCoefficientSupportedFiberLaurentUnitIso f T
  naturality := boundedFlatCoefficientSupportedFiberLaurentUnitIso_coefficient f T

/-- The same ambient forward unit before changing to coarse relative-open weakness. -/
def boundedFlatCoefficientSupportedAmbientLaurentAction :
    LaurentSeed.ModelAction (boundedFlatCoefficientSupportedAmbientModelFunctor T) where
  unit := boundedFlatCoefficientSupportedAmbientLaurentUnitIso Q T
  naturality := boundedFlatCoefficientSupportedAmbientLaurentUnitIso_coefficient Q T

/-- The original intersection-support Bass seed uses the actual square and source null. -/
def boundedFlatCoefficientSupportedFiberBassSeed :
    boundedFlatCoefficientSupportedFiberPrespectrumFunctor f T ⟶
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
        (boundedFlatCoefficientSupportedFiberPrespectrumFunctor f T) :=
  (boundedFlatCoefficientSupportedFiberLaurentAction f T).track.seed

/-- The original fine supported ambient Bass seed, with the same scalar/null concatenation. -/
def boundedFlatCoefficientSupportedAmbientBassSeed :
    boundedFlatCoefficientSupportedAmbientPrespectrumFunctor (Q := Q) T ⟶
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
        (boundedFlatCoefficientSupportedAmbientPrespectrumFunctor (Q := Q) T) :=
  (boundedFlatCoefficientSupportedAmbientLaurentAction T).track.seed

private theorem supportedFiberForget_unit_preserves (a : Under R)
    (r : (Γ(Spec a.right, ⊤))ˣ) :
    Preserves (boundedFlatCoefficientSupportedFiberForget f T a)
      (boundedFlatCoefficientSupportSectionUnitIso (boundedFlatCoefficientFiberSupportOpen f T a).ι
        r)
      (boundedFlatCoefficientSupportSectionUnitIso (boundedFlatCoefficientSupportOpen Q T a).ι r) :=
        by
  intro S
  apply ObjectProperty.hom_ext
  change ((boundedFlatCoefficientSupportSectionUnitIso
    (boundedFlatCoefficientFiberSupportOpen f T a).ι r).hom.app S).hom =
    ((boundedFlatCoefficientSupportSectionUnitIso
      (boundedFlatCoefficientSupportOpen Q T a).ι r).hom.app
      ((boundedFlatCoefficientSupportedFiberForget f T a).obj S)).hom
  rw [boundedFlatCoefficientSupportSectionUnitIso_hom,
    boundedFlatCoefficientSupportSectionUnitIso_hom]
  rfl

/-- The literal support inclusion preserves every original Laurent-action time and level. -/
theorem boundedFlatCoefficientSupportedFiberForget_laurent_apply
    (a : Under R) (n : ℕ) (t : unitInterval)
    (x : ((boundedFlatCoefficientSupportedFiberPrespectrumFunctor f T).obj a).space n) :
    ((boundedFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T).app
      ((laurentUnderFunctor R).obj a)).map n
      (((boundedFlatCoefficientSupportedFiberLaurentAction f T).track.homotopy a).level n (t, x)) =
    ((boundedFlatCoefficientSupportedAmbientLaurentAction T).track.homotopy a).level n
      (t, ((boundedFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T).app a).map n x)
        :=
  LaurentSeed.ModelAction.track_square (boundedFlatCoefficientSupportedFiberLaurentAction f T)
    (boundedFlatCoefficientSupportedAmbientLaurentAction T)
    (boundedFlatCoefficientSupportedFiberForgetModelTransformation f T)
    (fun a ↦ by
      change Preserves (boundedFlatCoefficientSupportedFiberForget f T
        ((laurentUnderFunctor R).obj a))
        (boundedFlatCoefficientSupportedFiberLaurentUnitIso f T a)
        (boundedFlatCoefficientSupportedAmbientLaurentUnitIso Q T a)
      simpa only [boundedFlatCoefficientSupportedFiberLaurentAction,
        boundedFlatCoefficientSupportedAmbientLaurentAction,
        boundedFlatCoefficientSupportedFiberLaurentUnitIso,
        boundedFlatCoefficientSupportedAmbientLaurentUnitIso,
        boundedFlatCoefficientSupportSectionUnitIso, boundedFlatCoefficientSectionLaurentUnitIso]
        using supportedFiberForget_unit_preserves f T ((laurentUnderFunctor R).obj a)
          (laurentGlobalUnit a.right)) a n t x

/-- Actual intersection-support inclusion preserves its unchanged whole Bass seed. -/
theorem boundedFlatCoefficientSupportedFiberBassSeed_forget :
    boundedFlatCoefficientSupportedFiberBassSeed f T ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T) =
    boundedFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T ≫
      boundedFlatCoefficientSupportedAmbientBassSeed T :=
  LaurentSeed.Track.seed_square (boundedFlatCoefficientSupportedFiberLaurentAction f T).track
    (boundedFlatCoefficientSupportedAmbientLaurentAction T).track
    (boundedFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T)
    (boundedFlatCoefficientSupportedFiberForget_laurent_apply f T)

omit [IsOpenImmersion f.left] in
private theorem supportedAmbientOpen_laurent_apply
    (a : Under R) (n : ℕ) (t : unitInterval)
    (x : ((boundedFlatCoefficientSupportedAmbientPrespectrumFunctor (Q := Q) T).obj a).space n) :
    ((boundedFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T).app
      ((laurentUnderFunctor R).obj a)).map n
      (((boundedFlatCoefficientSupportedAmbientLaurentAction T).track.homotopy a).level n (t, x)) =
    (boundedFlatCoefficientSupportedOpenLaurentHomotopy f T a).level n
      (t, ((boundedFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T).app a).map n x)
        :=
  LaurentSeed.ModelAction.track_square (boundedFlatCoefficientSupportedAmbientLaurentAction T)
    (boundedFlatCoefficientSupportedOpenLaurentAction f T)
    (boundedFlatCoefficientSupportedOpenChangeWeakModelTransformation f T) (fun _ _ ↦ rfl) a n t x

omit [IsOpenImmersion f.left] in
/-- Original supported ambient change of weakness preserves the same whole Bass seed. -/
theorem boundedFlatCoefficientSupportedAmbientBassSeed_open :
    boundedFlatCoefficientSupportedAmbientBassSeed T ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T) =
    boundedFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T ≫
      boundedFlatCoefficientSupportedOpenBassSeed f T :=
  LaurentSeed.Track.seed_square (boundedFlatCoefficientSupportedAmbientLaurentAction T).track
    (boundedFlatCoefficientSupportedOpenLaurentAction f T).track
    (boundedFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T)
    (supportedAmbientOpen_laurent_apply f T)

private theorem supportedFiberOpenNull_unitCompatible (a : Under R) :
    ZeroNullUnitCompatible
      ((boundedFlatCoefficientSupportedFiberForgetModelTransformation f T).app a)
      ((boundedFlatCoefficientSupportedOpenChangeWeakModelTransformation f T).app a)
      ((boundedFlatCoefficientSupportedFiberOpenDiagramNull f T).homotopy a) :=
  prespectrumCompositeZeroNullHomotopy_unitCompatible
    ((boundedFlatCoefficientSupportedFiberForgetModelTransformation f T).app a)
    ((boundedFlatCoefficientSupportedOpenChangeWeakModelTransformation f T).app a)
    (boundedFlatCoefficientSupportedFiberZeroToOpen f T a)
    (boundedFlatCoefficientSupportedFiberZeroToOpen_weak f T a)

private theorem supportedFiberOpenNull_unitInterchange
    (a : Under R) (r : (Γ(Spec a.right, ⊤))ˣ) :
    IdentityActionInterchange
      (V := (boundedFlatCoefficientSupportedFiberModelFunctor f T).obj a)
      (T := (boundedFlatCoefficientSupportedOpenModelFunctor f T).obj a)
      ((boundedFlatCoefficientSupportedFiberOpenDiagramNull f T).homotopy a)
      (boundedFlatCoefficientSupportSectionUnitIso (boundedFlatCoefficientFiberSupportOpen f T a).ι
        r)
      (boundedFlatCoefficientSupportSectionUnitIso (boundedFlatCoefficientSupportOpen Q T a).ι r) :=
  supportedFiberOpenNull_unitCompatible f T a _ _
    (supportedFiberForget_unit_preserves f T a r)

private theorem supportedFiberOpenNull_laurentInterchange (a : Under R) :
    TrackInterchange ((boundedFlatCoefficientSupportedFiberOpenDiagramNull f T).homotopy a)
      ((boundedFlatCoefficientSupportedFiberOpenDiagramNull f T).homotopy
        ((laurentUnderFunctor R).obj a))
      ((boundedFlatCoefficientSupportedFiberLaurentAction f T).track.homotopy a)
      (boundedFlatCoefficientSupportedOpenLaurentHomotopy f T a) :=
  modelDiagramNull_coefficientCompatible
    (r := boundedFlatCoefficientSupportedFiberForgetModelTransformation f T)
    (q := boundedFlatCoefficientSupportedOpenChangeWeakModelTransformation f T)
    (boundedFlatCoefficientSupportedFiberOpenDiagramNull f T) ((laurentUnderCoefficient R).app a)
    ((boundedFlatCoefficientSupportedFiberLaurentAction f T).unit a)
    ((boundedFlatCoefficientSupportedOpenLaurentAction f T).unit a)
    (by
      simpa only [boundedFlatCoefficientSupportedFiberLaurentAction,
        boundedFlatCoefficientSupportedOpenLaurentAction,
        boundedFlatCoefficientSupportedFiberLaurentUnitIso,
        boundedFlatCoefficientSupportedAmbientLaurentUnitIso,
        boundedFlatCoefficientSupportSectionUnitIso, boundedFlatCoefficientSectionLaurentUnitIso]
        using supportedFiberOpenNull_unitInterchange f T ((laurentUnderFunctor R).obj a)
          (laurentGlobalUnit a.right))

/-- Every original support localization-null time gives its actual coefficient transformation. -/
def boundedFlatCoefficientSupportedFiberOpenNullTimeSlice (s : unitInterval) :
    boundedFlatCoefficientSupportedFiberPrespectrumFunctor f T ⟶
      boundedFlatCoefficientSupportedOpenPrespectrumFunctor f T :=
  diagramHomotopyAt
    (η := boundedFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T ≫
      boundedFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T)
    (θ := diagramZeroMap (boundedFlatCoefficientSupportedFiberPrespectrumFunctor f T)
      (boundedFlatCoefficientSupportedOpenPrespectrumFunctor f T))
    (boundedFlatCoefficientSupportedFiberOpenDiagramNull f T).homotopy
    (boundedFlatCoefficientSupportedFiberOpenDiagramNull f T).naturality s

/-- Every time of this same original whole support null satisfies the actual seed square. -/
theorem boundedFlatCoefficientSupportedFiberOpenNullTimeSlice_seed (s : unitInterval) :
    boundedFlatCoefficientSupportedFiberBassSeed f T ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedFlatCoefficientSupportedFiberOpenNullTimeSlice f T s) =
    boundedFlatCoefficientSupportedFiberOpenNullTimeSlice f T s ≫
      boundedFlatCoefficientSupportedOpenBassSeed f T :=
  LaurentSeed.Track.seed_square (boundedFlatCoefficientSupportedFiberLaurentAction f T).track
    (boundedFlatCoefficientSupportedOpenLaurentAction f T).track
    (boundedFlatCoefficientSupportedFiberOpenNullTimeSlice f T s)
    (fun a n t x ↦ supportedFiberOpenNull_laurentInterchange f T a n s t x)

end Quillen.PerfectComplexes
