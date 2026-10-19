/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSectionFirstConeEvaluationLaurent

/-!
# Original first-cone Laurent evaluation regression

These tests retain the actual source and target first-step maps and distinguish
comparison time from both loop time and prespectrum structure time. They assert
no whole-cone extension or second-stage comparison.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.LoopPrespectrum Quillen.KTheory.Bass
open Quillen.PerfectComplexes Quillen.PerfectComplexes.CoefficientSectionFirstConeEvaluation
open CommRingCat.PolynomialLaurent
universe u
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
variable {a b : Under R} (g : a ⟶ b)

example (n : ℕ)
    (x : (parameterLooping ((boundedFlatCoefficientFullOpenPrespectrumFunctor f).obj
      ((laurentUnderFunctor R).obj a))).space n) :
    (firstLaurentNaturality f g).level n (0, x) =
      (firstLaurentInclusion f a ≫
        (((strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
          (boundedFlatCoefficientFullOpenPrespectrumFunctor f)).map g ≫
            firstEvaluation f b)).map n x :=
  (firstLaurentNaturality f g).at_zero n x

example (n : ℕ)
    (x : (parameterLooping ((boundedFlatCoefficientFullOpenPrespectrumFunctor f).obj
      ((laurentUnderFunctor R).obj a))).space n) :
    (firstLaurentNaturality f g).level n (1, x) =
      (firstLaurentInclusion f a ≫
        (firstEvaluation f a ≫ boundedFlatCoefficientBassStepMap P g)).map n x :=
  (firstLaurentNaturality f g).at_one n x

example (n : ℕ) (r t s : unitInterval)
    (x : (parameterLooping ((boundedFlatCoefficientFullOpenPrespectrumFunctor f).obj
      ((laurentUnderFunctor R).obj a))).space n) :
    Path.toContinuousMap ((firstLaurentNaturality f g).level (n + 1)
      (r, (parameterLooping ((boundedFlatCoefficientFullOpenPrespectrumFunctor f).obj
        ((laurentUnderFunctor R).obj a))).structureMap n x s)) t =
    Path.toContinuousMap ((boundedFlatCoefficientBassStep P b).structureMap n
      ((firstLaurentNaturality f g).level n (r, x)) s) t :=
  congrArg (fun y => Path.toContinuousMap y t) ((firstLaurentNaturality f g).comm n r x s)

example (r t : unitInterval) :
    Path.toContinuousMap ((firstLaurentNaturality f g).level 0
      (r, (parameterLooping ((boundedFlatCoefficientFullOpenPrespectrumFunctor f).obj
        ((laurentUnderFunctor R).obj a))).point 0)) t =
      Path.toContinuousMap ((boundedFlatCoefficientBassStep P b).point 0) t :=
  congrArg (fun y => Path.toContinuousMap y t) ((firstLaurentNaturality f g).at_point 0 r)
