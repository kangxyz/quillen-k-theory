/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientOpenBassSeed
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientOpenNull
public import Quillen.Waldhausen.SConstruction.Iterated.DiagramNullIdentityAction

/-!
# Whole compatibility of the actual global Bass seeds and canonical null

Original native restriction preserves the same coefficient-pulled unit. The grading map is
the original identity change of weakness. Both therefore preserve the complete Laurent tracks
and the original source-leg null cylinders, giving the two actual Bass seed squares.

For the very same canonical reversed zero-to-image null, identity-action interchange and
coefficient naturality retain independent scalar and null times. Each of its actual time
slices preserves the seed, including its prescribed concatenation and output-loop coordinate.
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
  [IsOpenImmersion f.left]
attribute [local irreducible] boundedFlatCoefficientOriginalEvaluation
  boundedFlatPerfectGlobalUnitIso boundedFlatCoefficientSectionLaurentUnitIso

/-- The actual restriction preserves each original forward Laurent-unit component. -/
theorem boundedFlatCoefficientOpenRestriction_laurentUnit (a : Under R) :
    Preserves
      ((boundedFlatCoefficientOpenRestrictionModelTransformation f).app
        ((laurentUnderFunctor R).obj a)).functor
      ((boundedFlatCoefficientOpenLaurentAction f).unit a)
      ((boundedFlatCoefficientFullOpenLaurentAction f).unit a) :=
  boundedFlatCoefficientSectionLaurentUnitIso_restriction f a

/-- Original native restriction preserves every level and the same Laurent-action time. -/
theorem boundedFlatCoefficientOpenRestriction_laurent_apply
    (a : Under R) (n : ℕ) (t : unitInterval)
    (x : ((boundedFlatCoefficientOpenPrespectrumFunctor f).obj a).space n) :
    ((boundedFlatCoefficientOpenRestrictionPrespectrumTransformation f).app
      ((laurentUnderFunctor R).obj a)).map n
        ((boundedFlatCoefficientOpenLaurentHomotopy f a).level n (t, x)) =
      (boundedFlatCoefficientFullOpenLaurentHomotopy f a).level n
        (t, ((boundedFlatCoefficientOpenRestrictionPrespectrumTransformation f).app a).map n x) :=
  LaurentSeed.ModelAction.track_square (boundedFlatCoefficientOpenLaurentAction f)
    (boundedFlatCoefficientFullOpenLaurentAction f)
    (boundedFlatCoefficientOpenRestrictionModelTransformation f)
    (boundedFlatCoefficientOpenRestriction_laurentUnit f) a n t x

/-- The actual coefficient-natural original restriction preserves the entire original Bass seed. -/
theorem boundedFlatCoefficientOpenBassSeed_restriction :
    boundedFlatCoefficientOpenBassSeed f ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedFlatCoefficientOpenRestrictionPrespectrumTransformation f) =
      boundedFlatCoefficientOpenRestrictionPrespectrumTransformation f ≫
        boundedFlatCoefficientFullOpenBassSeed f :=
  LaurentSeed.Track.seed_square (boundedFlatCoefficientOpenLaurentAction f).track
    (boundedFlatCoefficientFullOpenLaurentAction f).track
    (boundedFlatCoefficientOpenRestrictionPrespectrumTransformation f)
    (boundedFlatCoefficientOpenRestriction_laurent_apply f)

variable [CompactSpace P.left] [CompactSpace Q.left]

/-- The identity change of weakness retains the same original forward unit literally. -/
theorem boundedFlatCoefficientOpenGrading_laurentUnit (a : Under R) :
    Preserves
      ((boundedFlatCoefficientOpenGradingModelTransformation f).app
        ((laurentUnderFunctor R).obj a)).functor
      ((boundedFlatCoefficientFullOpenLaurentAction f).unit a)
      ((boundedFlatCoefficientGradedOpenLaurentAction f).unit a) := fun _ => rfl

/-- Original grading preserves every level and the same full Laurent-action time. -/
theorem boundedFlatCoefficientOpenGrading_laurent_apply
    (a : Under R) (n : ℕ) (t : unitInterval)
    (x : ((boundedFlatCoefficientFullOpenPrespectrumFunctor f).obj a).space n) :
    ((boundedFlatCoefficientOpenGradingPrespectrumTransformation f).app
      ((laurentUnderFunctor R).obj a)).map n
        ((boundedFlatCoefficientFullOpenLaurentHomotopy f a).level n (t, x)) =
      (boundedFlatCoefficientGradedOpenLaurentHomotopy f a).level n
        (t, ((boundedFlatCoefficientOpenGradingPrespectrumTransformation f).app a).map n x) :=
  LaurentSeed.ModelAction.track_square (boundedFlatCoefficientFullOpenLaurentAction f)
    (boundedFlatCoefficientGradedOpenLaurentAction f)
    (boundedFlatCoefficientOpenGradingModelTransformation f)
    (boundedFlatCoefficientOpenGrading_laurentUnit f) a n t x

/-- The actual coefficient-natural grading preserves the entire original Bass seed. -/
theorem boundedFlatCoefficientFullOpenBassSeed_grading :
    boundedFlatCoefficientFullOpenBassSeed f ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedFlatCoefficientOpenGradingPrespectrumTransformation f) =
      boundedFlatCoefficientOpenGradingPrespectrumTransformation f ≫
        boundedFlatCoefficientGradedOpenBassSeed f :=
  LaurentSeed.Track.seed_square (boundedFlatCoefficientFullOpenLaurentAction f).track
    (boundedFlatCoefficientGradedOpenLaurentAction f).track
    (boundedFlatCoefficientOpenGradingPrespectrumTransformation f)
    (boundedFlatCoefficientOpenGrading_laurent_apply f)

/-- The original zero-to-image realization supplies whole identity-action interchange. -/
theorem boundedFlatCoefficientOpenGradingNull_unitCompatible (a : Under R) :
    ZeroNullUnitCompatible
      ((boundedFlatCoefficientOpenRestrictionModelTransformation f).app a)
      ((boundedFlatCoefficientOpenGradingModelTransformation f).app a)
      ((boundedFlatCoefficientOpenGradingDiagramNull f).homotopy a) :=
  prespectrumCompositeZeroNullHomotopy_unitCompatible
    ((boundedFlatCoefficientOpenRestrictionModelTransformation f).app a)
    ((boundedFlatCoefficientOpenGradingModelTransformation f).app a)
    (boundedFlatCoefficientOpenZeroToGraded f a)
    (boundedFlatCoefficientOpenZeroToGraded_weak f a)

/-- The actual restriction and identity grading preserve every original coefficient unit. -/
theorem boundedFlatCoefficientOpenComposite_unit_preserves
    (a : Under R) (r : (Γ(Spec a.right, ⊤))ˣ) :
    Preserves
      (((boundedFlatCoefficientOpenRestrictionModelTransformation f).app a ≫
        (boundedFlatCoefficientOpenGradingModelTransformation f).app a).functor)
      (boundedFlatCoefficientSectionUnitIso (op Q, a)
        (boundedFlatCoefficientUnit (op Q, a) r))
      (boundedFlatCoefficientSectionUnitIso (op P, a)
        (boundedFlatCoefficientUnit (op P, a) r)) := by
  change Preserves (boundedFlatCoefficientOpenRestriction f a ⋙ 𝟭 _) _ _
  simpa only [Functor.comp_id, boundedFlatCoefficientOpenRestriction] using
    boundedFlatCoefficientSectionsRestriction_unit_preserves f a r

/-- The same canonical null interchanges with the actual forward coefficient units. -/
theorem boundedFlatCoefficientOpenGradingNull_unitInterchange
    (a : Under R) (r : (Γ(Spec a.right, ⊤))ˣ) :
    IdentityActionInterchange
      (V := (boundedFlatCoefficientOpenModelFunctor f).obj a)
      (T := (boundedFlatCoefficientGradedOpenModelFunctor f).obj a)
      ((boundedFlatCoefficientOpenGradingDiagramNull f).homotopy a)
      (boundedFlatCoefficientSectionUnitIso (op Q, a)
        (boundedFlatCoefficientUnit (op Q, a) r))
      (boundedFlatCoefficientSectionUnitIso (op P, a)
        (boundedFlatCoefficientUnit (op P, a) r)) :=
  boundedFlatCoefficientOpenGradingNull_unitCompatible f a _ _
    (boundedFlatCoefficientOpenComposite_unit_preserves f a r)

/-- Scalar and canonical-null times are independent on the two original Laurent tracks. -/
theorem boundedFlatCoefficientOpenGradingNull_laurentInterchange (a : Under R) :
    TrackInterchange
      ((boundedFlatCoefficientOpenGradingDiagramNull f).homotopy a)
      ((boundedFlatCoefficientOpenGradingDiagramNull f).homotopy
        ((laurentUnderFunctor R).obj a))
      (boundedFlatCoefficientOpenLaurentHomotopy f a)
      (boundedFlatCoefficientGradedOpenLaurentHomotopy f a) :=
  modelDiagramNull_coefficientCompatible
    (r := boundedFlatCoefficientOpenRestrictionModelTransformation f)
    (q := boundedFlatCoefficientOpenGradingModelTransformation f)
    (boundedFlatCoefficientOpenGradingDiagramNull f) ((laurentUnderCoefficient R).app a)
    ((boundedFlatCoefficientOpenLaurentAction f).unit a)
    ((boundedFlatCoefficientGradedOpenLaurentAction f).unit a)
    (by
      simpa only [boundedFlatCoefficientOpenLaurentAction,
        boundedFlatCoefficientGradedOpenLaurentAction, boundedFlatCoefficientSectionLaurentUnitIso]
        using boundedFlatCoefficientOpenGradingNull_unitInterchange f
          ((laurentUnderFunctor R).obj a) (laurentGlobalUnit a.right))

/-- Each time slice of the same canonical null remains an original coefficient transformation. -/
def boundedFlatCoefficientOpenGradingNullTimeSlice (s : unitInterval) :
    boundedFlatCoefficientOpenPrespectrumFunctor f ⟶
      boundedFlatCoefficientGradedOpenPrespectrumFunctor f :=
  diagramHomotopyAt
    (η := boundedFlatCoefficientOpenRestrictionPrespectrumTransformation f ≫
      boundedFlatCoefficientOpenGradingPrespectrumTransformation f)
    (θ := diagramZeroMap (boundedFlatCoefficientOpenPrespectrumFunctor f)
      (boundedFlatCoefficientGradedOpenPrespectrumFunctor f))
    (boundedFlatCoefficientOpenGradingDiagramNull f).homotopy
    (boundedFlatCoefficientOpenGradingDiagramNull f).naturality s

/-- Every time of the original canonical null satisfies the actual original seed square. -/
theorem boundedFlatCoefficientOpenGradingNullTimeSlice_seed (s : unitInterval) :
    boundedFlatCoefficientOpenBassSeed f ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedFlatCoefficientOpenGradingNullTimeSlice f s) =
      boundedFlatCoefficientOpenGradingNullTimeSlice f s ≫
        boundedFlatCoefficientGradedOpenBassSeed f :=
  LaurentSeed.Track.seed_square (boundedFlatCoefficientOpenLaurentAction f).track
    (boundedFlatCoefficientGradedOpenLaurentAction f).track
    (boundedFlatCoefficientOpenGradingNullTimeSlice f s)
    (fun a n t x => boundedFlatCoefficientOpenGradingNull_laurentInterchange f a n s t x)

/-- The Bass image of the same canonical null, on the actual original coefficient squares. -/
def boundedFlatCoefficientOpenGradingBassNullHomotopy (a : Under R) :=
  strictDiagramNullHomotopy
    (boundedFlatCoefficientOpenRestrictionPrespectrumTransformation f)
    (boundedFlatCoefficientOpenGradingPrespectrumTransformation f)
    (boundedFlatCoefficientOpenGradingDiagramNull f).homotopy
    (boundedFlatCoefficientOpenGradingDiagramNull f).naturality
    (laurentUnderSquareFunctor R) a

/-- The Bass null retains the same original natural time-slice map. -/
theorem boundedFlatCoefficientOpenGradingBassNullHomotopy_at (a : Under R) (s : unitInterval) :
    (boundedFlatCoefficientOpenGradingBassNullHomotopy f a).at s =
      ((strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedFlatCoefficientOpenGradingNullTimeSlice f s)).app a :=
  strictDiagramMapHomotopy_at
    (η := boundedFlatCoefficientOpenRestrictionPrespectrumTransformation f ≫
      boundedFlatCoefficientOpenGradingPrespectrumTransformation f)
    (θ := diagramZeroMap (boundedFlatCoefficientOpenPrespectrumFunctor f)
      (boundedFlatCoefficientGradedOpenPrespectrumFunctor f))
    (boundedFlatCoefficientOpenGradingDiagramNull f).homotopy
    (boundedFlatCoefficientOpenGradingDiagramNull f).naturality (laurentUnderSquareFunctor R) a s

/-- The canonical null and original seeds commute as complete based-loop values. -/
theorem boundedFlatCoefficientOpenGradingBassNullHomotopy_seed
    (a : Under R) (n : ℕ) (s : unitInterval)
    (x : ((boundedFlatCoefficientOpenPrespectrumFunctor f).obj a).space n) :
    (boundedFlatCoefficientOpenGradingBassNullHomotopy f a).level n
      (s, (boundedFlatCoefficientOpenBassSeedMap f a).map n x) =
      (boundedFlatCoefficientGradedOpenBassSeedMap f a).map n
        (((boundedFlatCoefficientOpenGradingDiagramNull f).homotopy a).level n (s, x)) := by
  have hs := congrArg (fun g => g.map n
    ((boundedFlatCoefficientOpenBassSeedMap f a).map n x))
    (boundedFlatCoefficientOpenGradingBassNullHomotopy_at f a s)
  exact hs.trans (congrArg (fun g => (g.app a).map n x)
    (boundedFlatCoefficientOpenGradingNullTimeSlice_seed f s))

/-- Null time and output-loop coordinate remain independent in the exact original seed equation. -/
theorem boundedFlatCoefficientOpenGradingBassNullHomotopy_seed_apply
    (a : Under R) (n : ℕ) (s t : unitInterval)
    (x : ((boundedFlatCoefficientOpenPrespectrumFunctor f).obj a).space n) :
    Path.toContinuousMap ((boundedFlatCoefficientOpenGradingBassNullHomotopy f a).level n
      (s, (boundedFlatCoefficientOpenBassSeedMap f a).map n x)) t =
      Path.toContinuousMap ((boundedFlatCoefficientGradedOpenBassSeedMap f a).map n
        (((boundedFlatCoefficientOpenGradingDiagramNull f).homotopy a).level n (s, x))) t :=
  congrArg (fun p => Path.toContinuousMap p t)
    (boundedFlatCoefficientOpenGradingBassNullHomotopy_seed f a n s x)

end Quillen.PerfectComplexes
