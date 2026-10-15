/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientOpenSeedCompatibility
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientOpenConeStable
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientGradedLaurentContraction
public import Quillen.KTheory.Bass.ModelDiagramIterateCofiberPreservation
public import Quillen.KTheory.Bass.StrictDiagramIterateNullTimeSlice

/-!
# Original finite global C/F/G Bass stages and whole null transitions

Every stage, transition and r/q map is the unchanged strict Bass iterate of the
actual global Model diagram and its original seed. The exact original canonical
localization null is iterated with all its times retained. Its proved seed-time
square supplies the whole finite transition equations. Actual finite Model
excision and the initial cone comparison give stable finite cone descents.
Separately, the constructed original graded seed null gives whole transition
nulls; no finite-stage vanishing or seed-stability premise is assumed.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

/-- Original finite C stages of the actual coarse native coefficient Model diagram. -/
def boundedFlatCoefficientOpenBassDiagram (i : ℕ) : Under R ⥤ LoopPrespectrum.{u+1} :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).obj
    (boundedFlatCoefficientOpenPrespectrumFunctor f)

/-- Original finite F stages of the same native fine open Model row. -/
def boundedFlatCoefficientFullOpenBassDiagram (i : ℕ) : Under R ⥤ LoopPrespectrum.{u+1} :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).obj
    (boundedFlatCoefficientFullOpenPrespectrumFunctor f)

/-- Every actual C transition is the original iterated coarse seed. -/
def boundedFlatCoefficientOpenBassTransition (i : ℕ) :
    boundedFlatCoefficientOpenBassDiagram f i ⟶ boundedFlatCoefficientOpenBassDiagram f (i + 1) :=
  strictDiagramTransition (laurentUnderSquareFunctor R) (boundedFlatCoefficientOpenBassSeed f) i

/-- Every actual F transition is the original iterated fine seed. -/
def boundedFlatCoefficientFullOpenBassTransition (i : ℕ) :
    boundedFlatCoefficientFullOpenBassDiagram f i ⟶
      boundedFlatCoefficientFullOpenBassDiagram f (i + 1) :=
  strictDiagramTransition (laurentUnderSquareFunctor R)
    (boundedFlatCoefficientFullOpenBassSeed f) i

/-- The same original r transformation at every finite stage. -/
def boundedFlatCoefficientOpenBassRestriction (i : ℕ) :
    boundedFlatCoefficientOpenBassDiagram f i ⟶ boundedFlatCoefficientFullOpenBassDiagram f i :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).map
    (boundedFlatCoefficientOpenRestrictionPrespectrumTransformation f)

/-- The actual r seed square supplies every unchanged finite transition equation. -/
theorem boundedFlatCoefficientOpenBassRestriction_transition (i : ℕ) :
    boundedFlatCoefficientOpenBassRestriction f i ≫
        boundedFlatCoefficientFullOpenBassTransition f i =
      boundedFlatCoefficientOpenBassTransition f i ≫
        boundedFlatCoefficientOpenBassRestriction f (i + 1) :=
  (strictDiagramTransition_map (laurentUnderSquareFunctor R)
    (boundedFlatCoefficientOpenBassSeed f) (boundedFlatCoefficientFullOpenBassSeed f)
    (boundedFlatCoefficientOpenRestrictionPrespectrumTransformation f)
    (boundedFlatCoefficientOpenBassSeed_restriction f) i).symm

/-- Actual finite Model growth supplies excision for the original finite restriction. -/
theorem boundedFlatCoefficientOpenBassRestriction_coneFiber_isStableEquivalence
    (i : ℕ) (a : Under R) : IsStableEquivalence
      (mappingConeFiberComparison ((boundedFlatCoefficientOpenBassRestriction f i).app a)) :=
  modelDiagramIterateArrow_coneFiber_isStableEquivalence (laurentUnderSquareFunctor R)
    (boundedFlatCoefficientOpenModelFunctor f) (boundedFlatCoefficientFullOpenModelFunctor f)
    (boundedFlatCoefficientOpenRestrictionPrespectrumTransformation f) i a

variable [CompactSpace P.left] [CompactSpace Q.left]

/-- Original finite G stages of the unchanged raw-image-quotient graded Model diagram. -/
def boundedFlatCoefficientGradedOpenBassDiagram (i : ℕ) : Under R ⥤ LoopPrespectrum.{u+1} :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).obj
    (boundedFlatCoefficientGradedOpenPrespectrumFunctor f)

/-- Every actual G transition is the unchanged iterated original graded seed. -/
def boundedFlatCoefficientGradedOpenBassTransition (i : ℕ) :
    boundedFlatCoefficientGradedOpenBassDiagram f i ⟶
      boundedFlatCoefficientGradedOpenBassDiagram f (i + 1) :=
  strictDiagramTransition (laurentUnderSquareFunctor R)
    (boundedFlatCoefficientGradedOpenBassSeed f) i

/-- The same original q transformation at every finite stage. -/
def boundedFlatCoefficientOpenBassGrading (i : ℕ) :
    boundedFlatCoefficientFullOpenBassDiagram f i ⟶
      boundedFlatCoefficientGradedOpenBassDiagram f i :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).map
    (boundedFlatCoefficientOpenGradingPrespectrumTransformation f)

/-- The actual q seed square supplies every unchanged finite transition equation. -/
theorem boundedFlatCoefficientOpenBassGrading_transition (i : ℕ) :
    boundedFlatCoefficientOpenBassGrading f i ≫ boundedFlatCoefficientGradedOpenBassTransition f i =
      boundedFlatCoefficientFullOpenBassTransition f i ≫
        boundedFlatCoefficientOpenBassGrading f (i + 1) :=
  (strictDiagramTransition_map (laurentUnderSquareFunctor R)
    (boundedFlatCoefficientFullOpenBassSeed f) (boundedFlatCoefficientGradedOpenBassSeed f)
    (boundedFlatCoefficientOpenGradingPrespectrumTransformation f)
    (boundedFlatCoefficientFullOpenBassSeed_grading f) i).symm

/-- Iterate precisely the original canonical whole coefficient-natural localization null. -/
def boundedFlatCoefficientOpenBassGradingNull (i : ℕ) :
    DiagramNullHomotopy (boundedFlatCoefficientOpenBassRestriction f i)
      (boundedFlatCoefficientOpenBassGrading f i) :=
  strictDiagramIterateNull (laurentUnderSquareFunctor R)
    (boundedFlatCoefficientOpenGradingDiagramNull f) i

/-- The whole finite localization null preserves original seed transitions at every time. -/
theorem boundedFlatCoefficientOpenBassGradingNull_transition
    (i : ℕ) (a : Under R) (m : ℕ) (s : unitInterval)
    (x : ((boundedFlatCoefficientOpenBassDiagram f i).obj a).space m) :
    ((boundedFlatCoefficientGradedOpenBassTransition f i).app a).map m
      (((boundedFlatCoefficientOpenBassGradingNull f i).homotopy a).level m (s, x)) =
    ((boundedFlatCoefficientOpenBassGradingNull f (i + 1)).homotopy a).level m
      (s, ((boundedFlatCoefficientOpenBassTransition f i).app a).map m x) :=
  (strictDiagramIterateNull_transition (laurentUnderSquareFunctor R)
    (boundedFlatCoefficientOpenGradingDiagramNull f)
    (boundedFlatCoefficientOpenBassSeed f) (boundedFlatCoefficientGradedOpenBassSeed f)
    (fun s ↦ boundedFlatCoefficientOpenGradingNullTimeSlice_seed f s) i a m s x).symm

/-- The actual finite original cone descends along the same complete iterated localization null. -/
def boundedFlatCoefficientOpenBassConeComparison (i : ℕ) :
    mappingConeDiagram (boundedFlatCoefficientOpenBassRestriction f i) ⟶
      boundedFlatCoefficientGradedOpenBassDiagram f i :=
  mappingConeDescTransformation (boundedFlatCoefficientOpenBassRestriction f i)
    (boundedFlatCoefficientOpenBassGrading f i)
    (boundedFlatCoefficientOpenBassGradingNull f i).homotopy
    (boundedFlatCoefficientOpenBassGradingNull f i).naturality

/-- The original finite cone inclusion has precisely the actual q_i face. -/
theorem boundedFlatCoefficientOpenBassConeComparison_inclusion (i : ℕ) (a : Under R) :
    mappingConeInclusion ((boundedFlatCoefficientOpenBassRestriction f i).app a) ≫
        (boundedFlatCoefficientOpenBassConeComparison f i).app a =
      (boundedFlatCoefficientOpenBassGrading f i).app a := mappingConeInclusion_desc _ _ _

/-- The original graded transition is whole-null through the actual original iterated seed null. -/
def boundedFlatCoefficientGradedOpenBassTransitionNull (i : ℕ) (a : Under R) :
    LoopPrespectrum.Homotopy ((boundedFlatCoefficientGradedOpenBassTransition f i).app a)
      (zeroHom ((boundedFlatCoefficientGradedOpenBassDiagram f i).obj a)
        ((boundedFlatCoefficientGradedOpenBassDiagram f (i + 1)).obj a)) :=
  ((strictDiagramIterateNull (laurentUnderSquareFunctor R)
    (boundedFlatCoefficientGradedOpenBassSeedDiagramNull f) i).homotopy a).cast (by
      let I := strictDiagramIterate (laurentUnderSquareFunctor R) i
      let B := (strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
        (boundedFlatCoefficientGradedOpenPrespectrumFunctor f)
      have hid : (I.map (𝟙 B)).app a = 𝟙 ((I.obj B).obj a) :=
        congrArg (fun η : I.obj B ⟶ I.obj B ↦ η.app a) (I.map_id B)
      exact (congrArg
        (fun g ↦ (I.map (boundedFlatCoefficientGradedOpenBassSeed f)).app a ≫ g)
        hid).trans (Category.comp_id _)) rfl

/-- Whole nullity of the original transition proves its signed stable map is zero. -/
theorem boundedFlatCoefficientGradedOpenBassTransition_stableMap_eq_zero
    (i : ℕ) (a : Under R) (d : ℤ) :
    (stableHomotopyFunctor d).map
      ((boundedFlatCoefficientGradedOpenBassTransition f i).app a) = 0 :=
  ((boundedFlatCoefficientGradedOpenBassTransitionNull f i a).stableHomotopyMap_eq d).trans
    (stableHomotopyMap_zero _ _ d)

variable [QuasiSeparatedSpace Q.left]

/-- Actual finite Model excision propagates the original initial stable cone descent. -/
theorem boundedFlatCoefficientOpenBassConeComparison_isStableEquivalence
    (i : ℕ) (a : Under R) :
    IsStableEquivalence ((boundedFlatCoefficientOpenBassConeComparison f i).app a) :=
  modelDiagramIterateCofiberDesc_isStableEquivalence (laurentUnderSquareFunctor R)
    (boundedFlatCoefficientOpenModelFunctor f) (boundedFlatCoefficientFullOpenModelFunctor f)
    (boundedFlatCoefficientGradedOpenModelFunctor f)
    (boundedFlatCoefficientOpenRestrictionPrespectrumTransformation f)
    (boundedFlatCoefficientOpenGradingPrespectrumTransformation f)
    (boundedFlatCoefficientOpenGradingDiagramNull f)
    (fun a ↦ boundedFlatCoefficientOpenConeComparison_isStableEquivalence f a) i a

end Quillen.PerfectComplexes
