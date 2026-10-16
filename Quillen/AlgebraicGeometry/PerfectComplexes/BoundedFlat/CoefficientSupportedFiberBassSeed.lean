/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.CoefficientFiberUnits


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
