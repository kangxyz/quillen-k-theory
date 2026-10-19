/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSectionEvaluationSeedComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassMap
public import Quillen.Topology.Prespectrum.ParameterLoopingHomotopy

/-!
# The Laurent face of first-cone evaluation naturality

The original fine-to-raw cone evaluation and the original coefficient cone maps
have a specified whole comparison on the Laurent inclusion. It is the unchanged
coefficient evaluation homotopy, followed by the original target cone inclusion.
Looping retains the independent comparison, loop, and structure parameters.

This is only the Laurent face needed for naturality of first-step evaluation.
It does not assert a homotopy on the whole source cone, the remaining moving
cone-null square, or a second-step evaluation/seed comparison.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.LoopPrespectrum Quillen.KTheory.Bass
open CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes.CoefficientSectionFirstConeEvaluation
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
variable {a b : Under R} (g : a ⟶ b)

/-- The original strict coefficient square map on the fine row. -/
def fineSquareMap : boundedFlatCoefficientFullOpenBassSquare f a ⟶
    boundedFlatCoefficientFullOpenBassSquare f b :=
  (boundedFlatCoefficientFullOpenPrespectrumFunctor f).mapArrow.mapArrow.map
    ((laurentUnderSquareFunctor R).map g)

/-- The original strict cone map before parameter looping. -/
def fineConeMap : boundedFlatCoefficientFullOpenBassCone f a ⟶
    boundedFlatCoefficientFullOpenBassCone f b :=
  mappingConeMap (strictSquareComparisonFunctor.map (fineSquareMap f g))

/-- The fine cone map retains the whole Laurent inclusion. -/
theorem fineConeMap_inclusion :
    mappingConeInclusion (StrictSquare.comparison
        (boundedFlatCoefficientFullOpenBassSquare f a)) ≫ fineConeMap f g =
      (boundedFlatCoefficientFullOpenPrespectrumFunctor f).map
        ((laurentUnderFunctor R).map g) ≫
          mappingConeInclusion (StrictSquare.comparison
            (boundedFlatCoefficientFullOpenBassSquare f b)) := by
  apply Hom.ext
  funext n
  ext x
  rfl

/-- The source Laurent restriction is the original fine coefficient map then evaluation. -/
theorem source_laurent :
    mappingConeInclusion (StrictSquare.comparison
        (boundedFlatCoefficientFullOpenBassSquare f a)) ≫
      (fineConeMap f g ≫ boundedFlatCoefficientFullOpenBassConeEvaluation f b) =
    ((boundedFlatCoefficientFullOpenPrespectrumFunctor f).map
        ((laurentUnderFunctor R).map g) ≫
      boundedFlatCoefficientSectionEvaluationPrespectrumMap
        (op P, (laurentUnderFunctor R).obj b)) ≫
      mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P b) := by
  rw [← Category.assoc, fineConeMap_inclusion, Category.assoc,
    boundedFlatCoefficientFullOpenBassConeEvaluation_inclusion, ← Category.assoc]

/-- The target Laurent restriction is evaluation then the original raw coefficient map. -/
theorem target_laurent :
    mappingConeInclusion (StrictSquare.comparison
        (boundedFlatCoefficientFullOpenBassSquare f a)) ≫
      (boundedFlatCoefficientFullOpenBassConeEvaluation f a ≫
        boundedFlatCoefficientBassConeMap P g) =
    (boundedFlatCoefficientSectionEvaluationPrespectrumMap
        (op P, (laurentUnderFunctor R).obj a) ≫
      boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map g))) ≫
      mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P b) := by
  rw [← Category.assoc, boundedFlatCoefficientFullOpenBassConeEvaluation_inclusion,
    Category.assoc, boundedFlatCoefficientBassConeMap_inclusion, ← Category.assoc]

/-- The specified Laurent face uses the original full evaluation track, without new pauses. -/
def laurentHomotopy :
    Homotopy
      (mappingConeInclusion (StrictSquare.comparison
          (boundedFlatCoefficientFullOpenBassSquare f a)) ≫
        (fineConeMap f g ≫ boundedFlatCoefficientFullOpenBassConeEvaluation f b))
      (mappingConeInclusion (StrictSquare.comparison
          (boundedFlatCoefficientFullOpenBassSquare f a)) ≫
        (boundedFlatCoefficientFullOpenBassConeEvaluation f a ≫
          boundedFlatCoefficientBassConeMap P g)) :=
  ((boundedFlatCoefficientSectionEvaluationHomotopy
    (R := R) (i := (op P, (laurentUnderFunctor R).obj a))
    (k := (op P, (laurentUnderFunctor R).obj b))
    (𝟙 (op P), (laurentUnderFunctor R).map g)).postcomp
      (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P b))).cast
        (source_laurent f g).symm (target_laurent f g).symm

/-- Every original Laurent point follows the same evaluation time. -/
theorem laurentHomotopy_apply (n : ℕ) (r : unitInterval)
    (x : ((boundedFlatCoefficientFullOpenPrespectrumFunctor f).obj
      ((laurentUnderFunctor R).obj a)).space n) :
    (laurentHomotopy f g).level n (r, x) =
      (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P b)).map n
        ((boundedFlatCoefficientSectionEvaluationHomotopy
          (R := R) (i := (op P, (laurentUnderFunctor R).obj a))
          (k := (op P, (laurentUnderFunctor R).obj b))
          (𝟙 (op P), (laurentUnderFunctor R).map g)).level n (r, x)) := rfl

/-- The unchanged first-stage fine-to-raw evaluation. -/
def firstEvaluation (a : Under R) :
    ((strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
      (boundedFlatCoefficientFullOpenPrespectrumFunctor f)).obj a ⟶
        boundedFlatCoefficientBassStep P a :=
  parameterLoopingMap (boundedFlatCoefficientFullOpenBassConeEvaluation f a)

/-- The original looped Laurent inclusion into the fine first stage. -/
def firstLaurentInclusion (a : Under R) :
    parameterLooping ((boundedFlatCoefficientFullOpenPrespectrumFunctor f).obj
      ((laurentUnderFunctor R).obj a)) ⟶
    ((strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
      (boundedFlatCoefficientFullOpenPrespectrumFunctor f)).obj a :=
  parameterLoopingMap (mappingConeInclusion
    (StrictSquare.comparison (boundedFlatCoefficientFullOpenBassSquare f a)))

/-- The full Laurent face of the proposed first-stage naturality, on the original maps. -/
def firstLaurentNaturality :
    Homotopy
      (firstLaurentInclusion f a ≫
        (((strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
          (boundedFlatCoefficientFullOpenPrespectrumFunctor f)).map g ≫ firstEvaluation f b))
      (firstLaurentInclusion f a ≫
        (firstEvaluation f a ≫ boundedFlatCoefficientBassStepMap P g)) :=
  (laurentHomotopy f g).parameterLooping.cast
    (by
      apply Hom.ext
      funext n
      apply ContinuousMap.ext
      intro x
      apply Path.ext
      funext t
      rfl)
    (by
      apply Hom.ext
      funext n
      apply ContinuousMap.ext
      intro x
      apply Path.ext
      funext t
      rfl)

/-- Comparison and loop times stay independent on every original Laurent loop. -/
theorem firstLaurentNaturality_apply (n : ℕ) (r t : unitInterval)
    (x : (parameterLooping ((boundedFlatCoefficientFullOpenPrespectrumFunctor f).obj
      ((laurentUnderFunctor R).obj a))).space n) :
    Path.toContinuousMap ((firstLaurentNaturality f g).level n (r, x)) t =
      (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P b)).map n
        ((boundedFlatCoefficientSectionEvaluationHomotopy
          (R := R) (i := (op P, (laurentUnderFunctor R).obj a))
          (k := (op P, (laurentUnderFunctor R).obj b))
          (𝟙 (op P), (laurentUnderFunctor R).map g)).level n
            (r, Path.toContinuousMap x t)) := rfl

end Quillen.PerfectComplexes.CoefficientSectionFirstConeEvaluation
