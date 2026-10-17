/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassActualSeedComparison
public import Quillen.Topology.Prespectrum.ConeHomotopySquare

/-! Objectwise Bass application to the original coefficient seed, with its chosen square track. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedIteration
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- The actual comparison homotopy supplies the full cone square null track. -/
def coneNull := mappingConeSquareNullHomotopy
  (boundedFlatCoefficientBassSquareComparison P a)
  (boundedFlatCoefficientBassSecondSquareComparison P a)
  (CoefficientBassSeedPushoutComparison.spanMap P a)
  (boundedFlatCoefficientBassTransition P ((laurentUnderFunctor R).obj a))
  (CoefficientBassActualSeedComparison.comparison P a)

/-- Bass applied to the seed before the outer parameter looping. -/
def coneMap := mappingConeSquareMap
  (boundedFlatCoefficientBassSquareComparison P a)
  (boundedFlatCoefficientBassSecondSquareComparison P a)
  (CoefficientBassSeedPushoutComparison.spanMap P a)
  (boundedFlatCoefficientBassTransition P ((laurentUnderFunctor R).obj a))
  (CoefficientBassActualSeedComparison.comparison P a)

/-- The genuine objectwise first-to-second Bass map induced by the original seed. -/
def stepMap : boundedFlatCoefficientBassStep P a ⟶
    boundedFlatCoefficientBassSecondStep P a :=
  parameterLoopingMap (coneMap P a)

/-- The actual Laurent inclusion is preserved by the chosen cone map. -/
theorem coneMap_inclusion :
    mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a) ≫ coneMap P a =
      boundedFlatCoefficientBassTransition P ((laurentUnderFunctor R).obj a) ≫
        mappingConeInclusion (boundedFlatCoefficientBassSecondSquareComparison P a) :=
  mappingConeSquareMap_inclusion _ _ _ _ _

/-- Every cylinder point retains the full square track followed by the target contraction. -/
theorem coneMap_cylinder (n : ℕ) (s : unitInterval)
    (x : (HomotopyPushout.prespectrum
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).space n) :
    (coneMap P a).map n
      (ReducedMappingCone.cylinder _ _
        ((boundedFlatCoefficientBassSquareComparison P a).map n) (s, x)) =
      (coneNull P a).level n (s, x) := rfl

/-- The looped inclusion square has the original Laurent seed as its upper map. -/
theorem stepMap_inclusion :
    parameterLoopingMap (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)) ≫
        stepMap P a =
      parameterLoopingMap
        (boundedFlatCoefficientBassTransition P ((laurentUnderFunctor R).obj a)) ≫
      boundedFlatCoefficientBassSecondLoopedInclusion P a :=
  mappingConeSquareMap_parameterLooping_inclusion _ _ _ _ _

/-- The output loop is evaluated by the same unlooped cone map at each independent loop time. -/
theorem stepMap_apply (n : ℕ) (x : (boundedFlatCoefficientBassStep P a).space n)
    (s : unitInterval) :
    Path.toContinuousMap ((stepMap P a).map n x) s =
      (coneMap P a).map n (Path.toContinuousMap x s) := rfl

end Quillen.PerfectComplexes.CoefficientBassSeedIteration
