/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedOpenBassSeed
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedOpenNull
public import Quillen.Waldhausen.SConstruction.Iterated.DiagramNullIdentityAction

/-!
# Actual auxiliary-supported seed squares and canonical whole-null compatibility

Supported restriction retains the original coefficient unit through the true
support square. Identity grading keeps the same supported open unit. Their
whole action tracks prove the original r_Z and q_Z Bass seed equations.

The same reversed zero-to-image null has identity-action interchange with
these supported scalar lifts. Scalar time, null time and output-loop coordinate
remain independent, and every actual null time slice preserves the same seed.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open Quillen.KTheory.Bass Quillen.FunctorIdentityAutomorphism
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)
attribute [local irreducible] boundedFlatCoefficientOriginalEvaluation
  boundedFlatPerfectGlobalUnitIso boundedFlatCoefficientSectionLaurentUnitIso

omit [IsOpenImmersion f.left] in
/-- The actual restriction preserves each original forward Laurent-unit component. -/
theorem boundedFlatCoefficientSupportedOpenRestriction_laurentUnit (a : Under R) :
    Preserves
      ((boundedFlatCoefficientSupportedOpenRestrictionModelTransformation f T).app
        ((laurentUnderFunctor R).obj a)).functor
      ((boundedFlatCoefficientSupportedOpenLaurentAction f T).unit a)
      ((boundedFlatCoefficientSupportedFullOpenLaurentAction f T).unit a) :=
  boundedFlatCoefficientSupportedOpenRestriction_laurentUnit_preserves f T a

omit [IsOpenImmersion f.left] in
/-- Original native restriction preserves every level and the same Laurent-action time. -/
theorem boundedFlatCoefficientSupportedOpenRestriction_laurent_apply
    (a : Under R) (n : ℕ) (t : unitInterval)
    (x : ((boundedFlatCoefficientSupportedOpenPrespectrumFunctor f T).obj a).space n) :
    ((boundedFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T).app
      ((laurentUnderFunctor R).obj a)).map n
        ((boundedFlatCoefficientSupportedOpenLaurentHomotopy f T a).level n (t, x)) =
      (boundedFlatCoefficientSupportedFullOpenLaurentHomotopy f T a).level n
        (t, ((boundedFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T).app
          a).map n x) :=
  LaurentSeed.ModelAction.track_square (boundedFlatCoefficientSupportedOpenLaurentAction f T)
    (boundedFlatCoefficientSupportedFullOpenLaurentAction f T)
    (boundedFlatCoefficientSupportedOpenRestrictionModelTransformation f T)
    (boundedFlatCoefficientSupportedOpenRestriction_laurentUnit f T) a n t x

omit [IsOpenImmersion f.left] in
/-- The actual coefficient-natural original restriction preserves the entire original Bass seed. -/
theorem boundedFlatCoefficientSupportedOpenBassSeed_restriction :
    boundedFlatCoefficientSupportedOpenBassSeed f T ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T) =
      boundedFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T ≫
        boundedFlatCoefficientSupportedFullOpenBassSeed f T :=
  LaurentSeed.Track.seed_square (boundedFlatCoefficientSupportedOpenLaurentAction f T).track
    (boundedFlatCoefficientSupportedFullOpenLaurentAction f T).track
    (boundedFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T)
    (boundedFlatCoefficientSupportedOpenRestriction_laurent_apply f T)

variable [CompactSpace P.left] [CompactSpace Q.left]

/-- The identity change of weakness retains the same original forward unit literally. -/
theorem boundedFlatCoefficientSupportedOpenGrading_laurentUnit (a : Under R) :
    Preserves
      ((boundedFlatCoefficientSupportedOpenGradingModelTransformation f T).app
        ((laurentUnderFunctor R).obj a)).functor
      ((boundedFlatCoefficientSupportedFullOpenLaurentAction f T).unit a)
      ((boundedFlatCoefficientSupportedGradedOpenLaurentAction f T).unit a) := fun _ => rfl

/-- Original grading preserves every level and the same full Laurent-action time. -/
theorem boundedFlatCoefficientSupportedOpenGrading_laurent_apply
    (a : Under R) (n : ℕ) (t : unitInterval)
    (x : ((boundedFlatCoefficientSupportedFullOpenPrespectrumFunctor f T).obj a).space n) :
    ((boundedFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T).app
      ((laurentUnderFunctor R).obj a)).map n
        ((boundedFlatCoefficientSupportedFullOpenLaurentHomotopy f T a).level n (t, x)) =
      (boundedFlatCoefficientSupportedGradedOpenLaurentHomotopy f T a).level n
        (t, ((boundedFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T).app a).map
          n x) :=
  LaurentSeed.ModelAction.track_square (boundedFlatCoefficientSupportedFullOpenLaurentAction f T)
    (boundedFlatCoefficientSupportedGradedOpenLaurentAction f T)
    (boundedFlatCoefficientSupportedOpenGradingModelTransformation f T)
    (boundedFlatCoefficientSupportedOpenGrading_laurentUnit f T) a n t x

/-- The actual coefficient-natural grading preserves the entire original Bass seed. -/
theorem boundedFlatCoefficientSupportedFullOpenBassSeed_grading :
    boundedFlatCoefficientSupportedFullOpenBassSeed f T ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T) =
      boundedFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T ≫
        boundedFlatCoefficientSupportedGradedOpenBassSeed f T :=
  LaurentSeed.Track.seed_square (boundedFlatCoefficientSupportedFullOpenLaurentAction f T).track
    (boundedFlatCoefficientSupportedGradedOpenLaurentAction f T).track
    (boundedFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T)
    (boundedFlatCoefficientSupportedOpenGrading_laurent_apply f T)

/-- The original zero-to-image realization supplies whole identity-action interchange. -/
theorem boundedFlatCoefficientSupportedOpenGradingNull_unitCompatible (a : Under R) :
    ZeroNullUnitCompatible
      ((boundedFlatCoefficientSupportedOpenRestrictionModelTransformation f T).app a)
      ((boundedFlatCoefficientSupportedOpenGradingModelTransformation f T).app a)
      ((boundedFlatCoefficientSupportedOpenGradingDiagramNull f T).homotopy a) :=
  prespectrumCompositeZeroNullHomotopy_unitCompatible
    ((boundedFlatCoefficientSupportedOpenRestrictionModelTransformation f T).app a)
    ((boundedFlatCoefficientSupportedOpenGradingModelTransformation f T).app a)
    (boundedFlatCoefficientSupportedOpenZeroToGraded f T a)
    (boundedFlatCoefficientSupportedOpenZeroToGraded_weak f T a)

/-- The actual restriction and identity grading preserve every original coefficient unit. -/
theorem boundedFlatCoefficientSupportedOpenComposite_unit_preserves
    (a : Under R) (r : (Γ(Spec a.right, ⊤))ˣ) :
    Preserves
      (((boundedFlatCoefficientSupportedOpenRestrictionModelTransformation f T).app a ≫
        (boundedFlatCoefficientSupportedOpenGradingModelTransformation f T).app a).functor)
      (boundedFlatCoefficientSupportSectionUnitIso (boundedFlatCoefficientSupportOpen Q T a).ι r)
      (boundedFlatCoefficientSupportSectionUnitIso (boundedFlatCoefficientOpenSupportOpen f T
        a).ι r) := by
  change Preserves (boundedFlatCoefficientSupportedOpenRestriction f T a ⋙ 𝟭 _) _ _
  simpa only [Functor.comp_id] using
    boundedFlatCoefficientSupportedOpenRestriction_coefficientUnit_preserves f T a r

/-- The same canonical null interchanges with the actual forward coefficient units. -/
theorem boundedFlatCoefficientSupportedOpenGradingNull_unitInterchange
    (a : Under R) (r : (Γ(Spec a.right, ⊤))ˣ) :
    IdentityActionInterchange
      (V := (boundedFlatCoefficientSupportedOpenModelFunctor f T).obj a)
      (T := (boundedFlatCoefficientSupportedGradedOpenModelFunctor f T).obj a)
      ((boundedFlatCoefficientSupportedOpenGradingDiagramNull f T).homotopy a)
      (boundedFlatCoefficientSupportSectionUnitIso (boundedFlatCoefficientSupportOpen Q T a).ι r)
      (boundedFlatCoefficientSupportSectionUnitIso (boundedFlatCoefficientOpenSupportOpen f T
        a).ι r) :=
  boundedFlatCoefficientSupportedOpenGradingNull_unitCompatible f T a _ _
    (boundedFlatCoefficientSupportedOpenComposite_unit_preserves f T a r)

/-- Scalar and canonical-null times are independent on the two original Laurent tracks. -/
theorem boundedFlatCoefficientSupportedOpenGradingNull_laurentInterchange (a : Under R) :
    TrackInterchange
      ((boundedFlatCoefficientSupportedOpenGradingDiagramNull f T).homotopy a)
      ((boundedFlatCoefficientSupportedOpenGradingDiagramNull f T).homotopy
        ((laurentUnderFunctor R).obj a))
      (boundedFlatCoefficientSupportedOpenLaurentHomotopy f T a)
      (boundedFlatCoefficientSupportedGradedOpenLaurentHomotopy f T a) :=
  modelDiagramNull_coefficientCompatible
    (r := boundedFlatCoefficientSupportedOpenRestrictionModelTransformation f T)
    (q := boundedFlatCoefficientSupportedOpenGradingModelTransformation f T)
    (boundedFlatCoefficientSupportedOpenGradingDiagramNull f T) ((laurentUnderCoefficient R).app a)
    ((boundedFlatCoefficientSupportedOpenLaurentAction f T).unit a)
    ((boundedFlatCoefficientSupportedGradedOpenLaurentAction f T).unit a)
    (by
      simpa only [boundedFlatCoefficientSupportedOpenLaurentAction,
        boundedFlatCoefficientSupportedGradedOpenLaurentAction,
        boundedFlatCoefficientSupportedAmbientLaurentUnitIso,
        boundedFlatCoefficientSupportedFullOpenLaurentUnitIso,
        boundedFlatCoefficientSupportSectionUnitIso, boundedFlatCoefficientSectionLaurentUnitIso]
        using boundedFlatCoefficientSupportedOpenGradingNull_unitInterchange f T
          ((laurentUnderFunctor R).obj a) (laurentGlobalUnit a.right))

/-- Each time slice of the same canonical null remains an original coefficient transformation. -/
def boundedFlatCoefficientSupportedOpenGradingNullTimeSlice (s : unitInterval) :
    boundedFlatCoefficientSupportedOpenPrespectrumFunctor f T ⟶
      boundedFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T :=
  diagramHomotopyAt
    (η := boundedFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T ≫
      boundedFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T)
    (θ := diagramZeroMap (boundedFlatCoefficientSupportedOpenPrespectrumFunctor f T)
      (boundedFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T))
    (boundedFlatCoefficientSupportedOpenGradingDiagramNull f T).homotopy
    (boundedFlatCoefficientSupportedOpenGradingDiagramNull f T).naturality s

/-- Every time of the original canonical null satisfies the actual original seed square. -/
theorem boundedFlatCoefficientSupportedOpenGradingNullTimeSlice_seed (s : unitInterval) :
    boundedFlatCoefficientSupportedOpenBassSeed f T ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedFlatCoefficientSupportedOpenGradingNullTimeSlice f T s) =
      boundedFlatCoefficientSupportedOpenGradingNullTimeSlice f T s ≫
        boundedFlatCoefficientSupportedGradedOpenBassSeed f T :=
  LaurentSeed.Track.seed_square (boundedFlatCoefficientSupportedOpenLaurentAction f T).track
    (boundedFlatCoefficientSupportedGradedOpenLaurentAction f T).track
    (boundedFlatCoefficientSupportedOpenGradingNullTimeSlice f T s)
    (fun a n t x => boundedFlatCoefficientSupportedOpenGradingNull_laurentInterchange f T a n s t x)

/-- The Bass image of the same canonical null, on the actual original coefficient squares. -/
def boundedFlatCoefficientSupportedOpenGradingBassNullHomotopy (a : Under R) :=
  strictDiagramNullHomotopy
    (boundedFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T)
    (boundedFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T)
    (boundedFlatCoefficientSupportedOpenGradingDiagramNull f T).homotopy
    (boundedFlatCoefficientSupportedOpenGradingDiagramNull f T).naturality
    (laurentUnderSquareFunctor R) a

/-- The Bass null retains the same original natural time-slice map. -/
theorem boundedFlatCoefficientSupportedOpenGradingBassNullHomotopy_at (a : Under R) (s :
  unitInterval) :
    (boundedFlatCoefficientSupportedOpenGradingBassNullHomotopy f T a).at s =
      ((strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedFlatCoefficientSupportedOpenGradingNullTimeSlice f T s)).app a :=
  strictDiagramMapHomotopy_at
    (η := boundedFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T ≫
      boundedFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T)
    (θ := diagramZeroMap (boundedFlatCoefficientSupportedOpenPrespectrumFunctor f T)
      (boundedFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T))
    (boundedFlatCoefficientSupportedOpenGradingDiagramNull f T).homotopy
    (boundedFlatCoefficientSupportedOpenGradingDiagramNull f T).naturality
      (laurentUnderSquareFunctor R) a s

/-- The canonical null and original seeds commute as complete based-loop values. -/
theorem boundedFlatCoefficientSupportedOpenGradingBassNullHomotopy_seed
    (a : Under R) (n : ℕ) (s : unitInterval)
    (x : ((boundedFlatCoefficientSupportedOpenPrespectrumFunctor f T).obj a).space n) :
    (boundedFlatCoefficientSupportedOpenGradingBassNullHomotopy f T a).level n
      (s, (boundedFlatCoefficientSupportedOpenBassSeedMap f T a).map n x) =
      (boundedFlatCoefficientSupportedGradedOpenBassSeedMap f T a).map n
        (((boundedFlatCoefficientSupportedOpenGradingDiagramNull f T).homotopy a).level n (s, x))
          := by
  have hs := congrArg (fun g => g.map n
    ((boundedFlatCoefficientSupportedOpenBassSeedMap f T a).map n x))
    (boundedFlatCoefficientSupportedOpenGradingBassNullHomotopy_at f T a s)
  exact hs.trans (congrArg (fun g => (g.app a).map n x)
    (boundedFlatCoefficientSupportedOpenGradingNullTimeSlice_seed f T s))

/-- Null time and output-loop coordinate remain independent in the exact original seed equation. -/
theorem boundedFlatCoefficientSupportedOpenGradingBassNullHomotopy_seed_apply
    (a : Under R) (n : ℕ) (s t : unitInterval)
    (x : ((boundedFlatCoefficientSupportedOpenPrespectrumFunctor f T).obj a).space n) :
    Path.toContinuousMap ((boundedFlatCoefficientSupportedOpenGradingBassNullHomotopy f T a).level n
      (s, (boundedFlatCoefficientSupportedOpenBassSeedMap f T a).map n x)) t =
      Path.toContinuousMap ((boundedFlatCoefficientSupportedGradedOpenBassSeedMap f T a).map n
        (((boundedFlatCoefficientSupportedOpenGradingDiagramNull f T).homotopy a).level n (s,
          x))) t :=
  congrArg (fun p => Path.toContinuousMap p t)
    (boundedFlatCoefficientSupportedOpenGradingBassNullHomotopy_seed f T a n s x)

end Quillen.PerfectComplexes
