/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedOpenSeedCompatibility
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedOpenConeStable
public import Quillen.KTheory.Bass.ModelDiagramIterateCofiberPreservation
public import Quillen.KTheory.Bass.StrictDiagramIterateNullTimeSlice

/-!
# Original finite auxiliary-supported C_Z/F_Z/G_Z Bass stages and whole null transitions

Every stage, transition and r/q map is the unchanged strict Bass iterate of the
actual auxiliary-supported Model diagram and its original seed. The original canonical
localization null is iterated with all its times retained. Its proved seed-time
square supplies the whole finite transition equations. Actual finite Model
excision and the initial cone comparison give stable finite cone descents.
Separately, the constructed original graded seed null gives whole transition
nulls; no finite-stage vanishing or seed-stability premise is assumed.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.PolynomialBaseChange
open Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- Original finite C_Z stages of the auxiliary-supported coarse coefficient Model diagram. -/
def boundedFlatCoefficientSupportedOpenBassDiagram (i : ℕ) : Under R ⥤ LoopPrespectrum.{u+1} :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).obj
    (boundedFlatCoefficientSupportedOpenPrespectrumFunctor f T)

/-- Original finite F stages of the same native fine open Model row. -/
def boundedFlatCoefficientSupportedFullOpenBassDiagram (i : ℕ) : Under R ⥤ LoopPrespectrum.{u+1} :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).obj
    (boundedFlatCoefficientSupportedFullOpenPrespectrumFunctor f T)

/-- Every actual C transition is the original iterated coarse seed. -/
def boundedFlatCoefficientSupportedOpenBassTransition (i : ℕ) :
    boundedFlatCoefficientSupportedOpenBassDiagram f T i ⟶
      boundedFlatCoefficientSupportedOpenBassDiagram f T (i + 1) :=
  strictDiagramTransition (laurentUnderSquareFunctor R) (boundedFlatCoefficientSupportedOpenBassSeed
    f T) i

/-- Every actual F transition is the original iterated fine seed. -/
def boundedFlatCoefficientSupportedFullOpenBassTransition (i : ℕ) :
    boundedFlatCoefficientSupportedFullOpenBassDiagram f T i ⟶
      boundedFlatCoefficientSupportedFullOpenBassDiagram f T (i + 1) :=
  strictDiagramTransition (laurentUnderSquareFunctor R)
    (boundedFlatCoefficientSupportedFullOpenBassSeed f T) i

/-- The same original r transformation at every finite stage. -/
def boundedFlatCoefficientSupportedOpenBassRestriction (i : ℕ) :
    boundedFlatCoefficientSupportedOpenBassDiagram f T i ⟶
      boundedFlatCoefficientSupportedFullOpenBassDiagram f T i :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).map
    (boundedFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T)

omit [IsOpenImmersion f.left] in
/-- The actual r seed square supplies every unchanged finite transition equation. -/
theorem boundedFlatCoefficientSupportedOpenBassRestriction_transition (i : ℕ) :
    boundedFlatCoefficientSupportedOpenBassRestriction f T i ≫
        boundedFlatCoefficientSupportedFullOpenBassTransition f T i =
      boundedFlatCoefficientSupportedOpenBassTransition f T i ≫
        boundedFlatCoefficientSupportedOpenBassRestriction f T (i + 1) :=
  (strictDiagramTransition_map (laurentUnderSquareFunctor R)
    (boundedFlatCoefficientSupportedOpenBassSeed f T)
      (boundedFlatCoefficientSupportedFullOpenBassSeed f T)
    (boundedFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T)
    (boundedFlatCoefficientSupportedOpenBassSeed_restriction f T) i).symm

omit [IsOpenImmersion f.left] in
/-- Actual finite Model growth supplies excision for the original finite restriction. -/
theorem boundedFlatCoefficientSupportedOpenBassRestriction_coneFiber_isStableEquivalence
    (i : ℕ) (a : Under R) : IsStableEquivalence
      (mappingConeFiberComparison ((boundedFlatCoefficientSupportedOpenBassRestriction f T i).app
        a)) :=
  modelDiagramIterateArrow_coneFiber_isStableEquivalence (laurentUnderSquareFunctor R)
    (boundedFlatCoefficientSupportedOpenModelFunctor f T)
      (boundedFlatCoefficientSupportedFullOpenModelFunctor f T)
    (boundedFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T) i a

variable [CompactSpace P.left] [CompactSpace Q.left]

/-- Original finite G stages of the unchanged raw-image-quotient graded Model diagram. -/
def boundedFlatCoefficientSupportedGradedOpenBassDiagram (i : ℕ) : Under R ⥤ LoopPrespectrum.{u+1}
  :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).obj
    (boundedFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T)

/-- Every actual G transition is the unchanged iterated original graded seed. -/
def boundedFlatCoefficientSupportedGradedOpenBassTransition (i : ℕ) :
    boundedFlatCoefficientSupportedGradedOpenBassDiagram f T i ⟶
      boundedFlatCoefficientSupportedGradedOpenBassDiagram f T (i + 1) :=
  strictDiagramTransition (laurentUnderSquareFunctor R)
    (boundedFlatCoefficientSupportedGradedOpenBassSeed f T) i

/-- The same original q transformation at every finite stage. -/
def boundedFlatCoefficientSupportedOpenBassGrading (i : ℕ) :
    boundedFlatCoefficientSupportedFullOpenBassDiagram f T i ⟶
      boundedFlatCoefficientSupportedGradedOpenBassDiagram f T i :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).map
    (boundedFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T)

/-- The actual q seed square supplies every unchanged finite transition equation. -/
theorem boundedFlatCoefficientSupportedOpenBassGrading_transition (i : ℕ) :
    boundedFlatCoefficientSupportedOpenBassGrading f T i ≫
      boundedFlatCoefficientSupportedGradedOpenBassTransition f T i =
      boundedFlatCoefficientSupportedFullOpenBassTransition f T i ≫
        boundedFlatCoefficientSupportedOpenBassGrading f T (i + 1) :=
  (strictDiagramTransition_map (laurentUnderSquareFunctor R)
    (boundedFlatCoefficientSupportedFullOpenBassSeed f T)
      (boundedFlatCoefficientSupportedGradedOpenBassSeed f T)
    (boundedFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T)
    (boundedFlatCoefficientSupportedFullOpenBassSeed_grading f T) i).symm

/-- Iterate precisely the original canonical whole coefficient-natural localization null. -/
def boundedFlatCoefficientSupportedOpenBassGradingNull (i : ℕ) :
    DiagramNullHomotopy (boundedFlatCoefficientSupportedOpenBassRestriction f T i)
      (boundedFlatCoefficientSupportedOpenBassGrading f T i) :=
  strictDiagramIterateNull (laurentUnderSquareFunctor R)
    (boundedFlatCoefficientSupportedOpenGradingDiagramNull f T) i

/-- The whole finite localization null preserves original seed transitions at every time. -/
theorem boundedFlatCoefficientSupportedOpenBassGradingNull_transition
    (i : ℕ) (a : Under R) (m : ℕ) (s : unitInterval)
    (x : ((boundedFlatCoefficientSupportedOpenBassDiagram f T i).obj a).space m) :
    ((boundedFlatCoefficientSupportedGradedOpenBassTransition f T i).app a).map m
      (((boundedFlatCoefficientSupportedOpenBassGradingNull f T i).homotopy a).level m (s, x)) =
    ((boundedFlatCoefficientSupportedOpenBassGradingNull f T (i + 1)).homotopy a).level m
      (s, ((boundedFlatCoefficientSupportedOpenBassTransition f T i).app a).map m x) :=
  (strictDiagramIterateNull_transition (laurentUnderSquareFunctor R)
    (boundedFlatCoefficientSupportedOpenGradingDiagramNull f T)
    (boundedFlatCoefficientSupportedOpenBassSeed f T)
      (boundedFlatCoefficientSupportedGradedOpenBassSeed f T)
    (fun s ↦ boundedFlatCoefficientSupportedOpenGradingNullTimeSlice_seed f T s) i a m s x).symm

/-- The actual finite original cone descends along the same complete iterated localization null. -/
def boundedFlatCoefficientSupportedOpenBassConeComparison (i : ℕ) :
    mappingConeDiagram (boundedFlatCoefficientSupportedOpenBassRestriction f T i) ⟶
      boundedFlatCoefficientSupportedGradedOpenBassDiagram f T i :=
  mappingConeDescTransformation (boundedFlatCoefficientSupportedOpenBassRestriction f T i)
    (boundedFlatCoefficientSupportedOpenBassGrading f T i)
    (boundedFlatCoefficientSupportedOpenBassGradingNull f T i).homotopy
    (boundedFlatCoefficientSupportedOpenBassGradingNull f T i).naturality

/-- The original finite cone inclusion has precisely the actual q_i face. -/
theorem boundedFlatCoefficientSupportedOpenBassConeComparison_inclusion (i : ℕ) (a : Under R) :
    mappingConeInclusion ((boundedFlatCoefficientSupportedOpenBassRestriction f T i).app a) ≫
        (boundedFlatCoefficientSupportedOpenBassConeComparison f T i).app a =
      (boundedFlatCoefficientSupportedOpenBassGrading f T i).app a := mappingConeInclusion_desc _ _
        _

/-- The original graded transition is whole-null through the actual original iterated seed null. -/
def boundedFlatCoefficientSupportedGradedOpenBassTransitionNull (i : ℕ) (a : Under R) :
    LoopPrespectrum.Homotopy ((boundedFlatCoefficientSupportedGradedOpenBassTransition f T i).app a)
      (zeroHom ((boundedFlatCoefficientSupportedGradedOpenBassDiagram f T i).obj a)
        ((boundedFlatCoefficientSupportedGradedOpenBassDiagram f T (i + 1)).obj a)) :=
  ((strictDiagramIterateNull (laurentUnderSquareFunctor R)
    (boundedFlatCoefficientSupportedGradedOpenBassSeedDiagramNull f T) i).homotopy a).cast (by
      let I := strictDiagramIterate (laurentUnderSquareFunctor R) i
      let B := (strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
        (boundedFlatCoefficientSupportedGradedOpenPrespectrumFunctor f T)
      have hid : (I.map (𝟙 B)).app a = 𝟙 ((I.obj B).obj a) :=
        congrArg (fun η : I.obj B ⟶ I.obj B ↦ η.app a) (I.map_id B)
      exact (congrArg
        (fun g ↦ (I.map (boundedFlatCoefficientSupportedGradedOpenBassSeed f T)).app a ≫ g)
        hid).trans (Category.comp_id _)) rfl

/-- Whole nullity of the original transition proves its signed stable map is zero. -/
theorem boundedFlatCoefficientSupportedGradedOpenBassTransition_stableMap_eq_zero
    (i : ℕ) (a : Under R) (d : ℤ) :
    (stableHomotopyFunctor d).map
      ((boundedFlatCoefficientSupportedGradedOpenBassTransition f T i).app a) = 0 :=
  ((boundedFlatCoefficientSupportedGradedOpenBassTransitionNull f T i a).stableHomotopyMap_eq
    d).trans
    (stableHomotopyMap_zero _ _ d)

variable [QuasiSeparatedSpace Q.left] [CompactSpace T]

/-- Actual finite Model excision propagates the original initial stable cone descent. -/
theorem boundedFlatCoefficientSupportedOpenBassConeComparison_isStableEquivalence
    (i : ℕ) (a : Under R) :
    IsStableEquivalence ((boundedFlatCoefficientSupportedOpenBassConeComparison f T i).app a) :=
  modelDiagramIterateCofiberDesc_isStableEquivalence (laurentUnderSquareFunctor R)
    (boundedFlatCoefficientSupportedOpenModelFunctor f T)
      (boundedFlatCoefficientSupportedFullOpenModelFunctor f T)
    (boundedFlatCoefficientSupportedGradedOpenModelFunctor f T)
    (boundedFlatCoefficientSupportedOpenRestrictionPrespectrumTransformation f T)
    (boundedFlatCoefficientSupportedOpenGradingPrespectrumTransformation f T)
    (boundedFlatCoefficientSupportedOpenGradingDiagramNull f T)
    (fun a ↦ boundedFlatCoefficientSupportedOpenGradingConeComparison_isStableEquivalence f T a) i a

end Quillen.PerfectComplexes
