/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassUnitCubeConsumers

/-! Strict consumers require whole original identity laws with no assumed interior filler. -/

public section
noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.PerfectComplexes
open Quillen.PerfectComplexes.CoefficientBassUnitCubeConsumers
open scoped Topology unitInterval
universe u
namespace QuillenTest.CoefficientBassUnitCubeConsumers
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- The original cone identity is a homotopy on the complete cone map. -/
def wholeOriginalConeIdentity : Homotopy (boundedFlatCoefficientBassConeMap P (𝟙 a))
    (𝟙 (mappingCone (boundedFlatCoefficientBassSquareComparison P a))) := coneIdentity P a

/-- The original step identity retains the complete parameter-looped cone map. -/
def wholeOriginalStepIdentity : Homotopy (boundedFlatCoefficientBassStepMap P (𝟙 a))
    (𝟙 (parameterLooping (mappingCone (boundedFlatCoefficientBassSquareComparison P a)))) :=
  stepIdentity P a

theorem original_laurent_track_zero (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj a)))).space 0) :
    (wholeOriginalConeIdentity P a).level 0
      (r, (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)).map 0 x) =
      (boundedFlatCoefficientBassConeIdentityInclusionHomotopy P a).level 0 (r, x) :=
  cone_inclusion P a 0 r x

end QuillenTest.CoefficientBassUnitCubeConsumers
