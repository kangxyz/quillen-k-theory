/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeCubeConsumers
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSectionEvaluationBassSeed

/-!
# The actual second native coefficient Bass object

The two chart tracks are the fixed whole composition homotopies of the original first-step
maps, cast only along the actual polynomial/Laurent projection equations. The comparison is
the original reduced homotopy-pushout descent, with the reversed positive track followed by
the inverse track. Its literal mapping cone and parameter-correct looping define the second
object. The positive source leg and null retain this same choice throughout.

This is an objectwise construction. A second coefficient map needs the higher compatibility
of the fixed composition tracks. Applying Bass to the original seed needs two different mixed
projection pastings between the original composition, seed naturality, and fixed first-step
composition. Neither of those constructions, nor their evaluation or null comparisons, is
supplied here.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.LoopPrespectrum CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- The positive chart uses the fixed whole first-step composition, with its exact source cast. -/
def boundedFlatCoefficientBassSecondPlusHomotopy :
    Homotopy (boundedFlatCoefficientBassStepMap P ((laurentUnderCoefficient R).app a))
      (boundedFlatCoefficientBassStepMap P ((polynomialUnderCoefficient R).app a) ≫
        boundedFlatCoefficientBassStepMap P ((underToLaurent R).app a)) :=
  (BassMWhole.stepComposition P ((polynomialUnderCoefficient R).app a)
    ((underToLaurent R).app a)).cast
      (congrArg (boundedFlatCoefficientBassStepMap P)
        (polynomialUnderCoefficient_toLaurent R a)) rfl

/-- The inverse chart retains the distinct fixed whole composition and its own source cast. -/
def boundedFlatCoefficientBassSecondMinusHomotopy :
    Homotopy (boundedFlatCoefficientBassStepMap P ((laurentUnderCoefficient R).app a))
      (boundedFlatCoefficientBassStepMap P ((polynomialUnderCoefficient R).app a) ≫
        boundedFlatCoefficientBassStepMap P ((underToLaurentInvert R).app a)) :=
  (BassMWhole.stepComposition P ((polynomialUnderCoefficient R).app a)
    ((underToLaurentInvert R).app a)).cast
      (congrArg (boundedFlatCoefficientBassStepMap P)
        (polynomialUnderCoefficient_toLaurentInvert R a)) rfl

/-- The second overlap follows the reversed positive track and then the inverse track. -/
def boundedFlatCoefficientBassSecondSquareHomotopy :=
  (boundedFlatCoefficientBassSecondPlusHomotopy P a).symm.trans
    (boundedFlatCoefficientBassSecondMinusHomotopy P a)

/-- Actual first-step polynomial and Laurent maps descend the original two-chart cylinder. -/
def boundedFlatCoefficientBassSecondSquareComparison :=
  HomotopyPushout.desc
    (boundedFlatCoefficientBassStepMap P ((polynomialUnderCoefficient R).app a))
    (boundedFlatCoefficientBassStepMap P ((polynomialUnderCoefficient R).app a))
    (boundedFlatCoefficientBassStepMap P ((underToLaurent R).app a))
    (boundedFlatCoefficientBassStepMap P ((underToLaurentInvert R).app a))
    (boundedFlatCoefficientBassSecondSquareHomotopy P a)

/-- The second native Bass object is parameter looping of this literal comparison cone. -/
def boundedFlatCoefficientBassSecondStep : LoopPrespectrum :=
  parameterLooping (mappingCone (boundedFlatCoefficientBassSecondSquareComparison P a))

/-- The actual positive first-step polynomial projection followed by the left inclusion. -/
def boundedFlatCoefficientBassSecondSourceLeg :=
  boundedFlatCoefficientBassStepMap P ((polynomialUnderCoefficient R).app a) ≫
    HomotopyPushout.inl
      (boundedFlatCoefficientBassStepMap P ((polynomialUnderCoefficient R).app a))
      (boundedFlatCoefficientBassStepMap P ((polynomialUnderCoefficient R).app a))

/-- Descent on the source leg is precisely the selected positive first-step composite. -/
theorem boundedFlatCoefficientBassSecondSourceLeg_comparison :
    boundedFlatCoefficientBassSecondSourceLeg P a ≫
        boundedFlatCoefficientBassSecondSquareComparison P a =
      boundedFlatCoefficientBassStepMap P ((polynomialUnderCoefficient R).app a) ≫
        boundedFlatCoefficientBassStepMap P ((underToLaurent R).app a) := by
  unfold boundedFlatCoefficientBassSecondSourceLeg boundedFlatCoefficientBassSecondSquareComparison
  rw [Category.assoc, HomotopyPushout.inl_desc]

/-- The literal Laurent inclusion into the second comparison cone, before outer looping. -/
def boundedFlatCoefficientBassSecondConeInclusion :
    boundedFlatCoefficientBassStep P ((laurentUnderFunctor R).obj a) ⟶
      mappingCone (boundedFlatCoefficientBassSecondSquareComparison P a) :=
  mappingConeInclusion (boundedFlatCoefficientBassSecondSquareComparison P a)

/-- Outer looping of the literal inclusion has the actual looped Laurent first-step domain. -/
def boundedFlatCoefficientBassSecondLoopedInclusion :
    parameterLooping (boundedFlatCoefficientBassStep P ((laurentUnderFunctor R).obj a)) ⟶
      boundedFlatCoefficientBassSecondStep P a :=
  parameterLoopingMap (boundedFlatCoefficientBassSecondConeInclusion P a)

/-- The fixed positive composition and actual cone contraction null the Laurent source map. -/
def boundedFlatCoefficientBassSecondLaurentNullHomotopy :
    Homotopy
      (boundedFlatCoefficientBassStepMap P ((laurentUnderCoefficient R).app a) ≫
        boundedFlatCoefficientBassSecondConeInclusion P a)
      (zeroHom (boundedFlatCoefficientBassStep P a)
        (mappingCone (boundedFlatCoefficientBassSecondSquareComparison P a))) := by
  have N := Homotopy.precomp (boundedFlatCoefficientBassSecondSourceLeg P a)
    (mappingConeHomotopy (boundedFlatCoefficientBassSecondSquareComparison P a))
  change Homotopy
    ((boundedFlatCoefficientBassSecondSourceLeg P a ≫
        boundedFlatCoefficientBassSecondSquareComparison P a) ≫
      boundedFlatCoefficientBassSecondConeInclusion P a) (zeroHom _ _) at N
  rw [boundedFlatCoefficientBassSecondSourceLeg_comparison] at N
  exact ((boundedFlatCoefficientBassSecondPlusHomotopy P a).postcomp
    (boundedFlatCoefficientBassSecondConeInclusion P a)).trans N

/-- Positive comparison time and the inner first-step loop time remain independent. -/
theorem boundedFlatCoefficientBassSecondPlusHomotopy_apply (n : ℕ) (r s : unitInterval)
    (x : (boundedFlatCoefficientBassStep P a).space n) :
    Path.toContinuousMap
      ((boundedFlatCoefficientBassSecondPlusHomotopy P a).level n (r, x)) s =
      (BassMWhole.coneComposition P ((polynomialUnderCoefficient R).app a)
        ((underToLaurent R).app a)).level n (r, Path.toContinuousMap x s) := rfl

/-- The inverse comparison retains the same independent coordinates on its distinct chart. -/
theorem boundedFlatCoefficientBassSecondMinusHomotopy_apply (n : ℕ) (r s : unitInterval)
    (x : (boundedFlatCoefficientBassStep P a).space n) :
    Path.toContinuousMap
      ((boundedFlatCoefficientBassSecondMinusHomotopy P a).level n (r, x)) s =
      (BassMWhole.coneComposition P ((polynomialUnderCoefficient R).app a)
        ((underToLaurentInvert R).app a)).level n (r, Path.toContinuousMap x s) := rfl

/-- The left chart descends to the actual positive first-step Laurent map. -/
theorem boundedFlatCoefficientBassSecondSquareComparison_inl :
    HomotopyPushout.inl
        (boundedFlatCoefficientBassStepMap P ((polynomialUnderCoefficient R).app a))
        (boundedFlatCoefficientBassStepMap P ((polynomialUnderCoefficient R).app a)) ≫
      boundedFlatCoefficientBassSecondSquareComparison P a =
    boundedFlatCoefficientBassStepMap P ((underToLaurent R).app a) :=
  HomotopyPushout.inl_desc _ _ _ _ _

/-- The right chart descends to the actual inverse first-step Laurent map. -/
theorem boundedFlatCoefficientBassSecondSquareComparison_inr :
    HomotopyPushout.inr
        (boundedFlatCoefficientBassStepMap P ((polynomialUnderCoefficient R).app a))
        (boundedFlatCoefficientBassStepMap P ((polynomialUnderCoefficient R).app a)) ≫
      boundedFlatCoefficientBassSecondSquareComparison P a =
    boundedFlatCoefficientBassStepMap P ((underToLaurentInvert R).app a) :=
  HomotopyPushout.inr_desc _ _ _ _ _

/-- The whole original overlap cylinder retains the selected ordered chart homotopy. -/
theorem boundedFlatCoefficientBassSecondSquareComparison_cylinder (n : ℕ) (r : unitInterval)
    (x : (boundedFlatCoefficientBassStep P a).space n) :
    (boundedFlatCoefficientBassSecondSquareComparison P a).map n
      (HomotopyPushout.cylinder
        (boundedFlatCoefficientBassStepMap P ((polynomialUnderCoefficient R).app a))
        (boundedFlatCoefficientBassStepMap P ((polynomialUnderCoefficient R).app a)) n (r, x)) =
      (boundedFlatCoefficientBassSecondSquareHomotopy P a).level n (r, x) := rfl

/-- Outer loop evaluation of the inclusion does not identify it with the inner first-step loop. -/
theorem boundedFlatCoefficientBassSecondLoopedInclusion_apply (n : ℕ) (r : unitInterval)
    (x : (parameterLooping
      (boundedFlatCoefficientBassStep P ((laurentUnderFunctor R).obj a))).space n) :
    Path.toContinuousMap ((boundedFlatCoefficientBassSecondLoopedInclusion P a).map n x) r =
      (boundedFlatCoefficientBassSecondConeInclusion P a).map n (Path.toContinuousMap x r) := rfl

/-- The second object's outer loop coordinate remains internal to its independent structure time. -/
theorem boundedFlatCoefficientBassSecondStep_structure (n : ℕ) (r t : unitInterval)
    (x : (boundedFlatCoefficientBassSecondStep P a).space n) :
    Path.toContinuousMap ((boundedFlatCoefficientBassSecondStep P a).structureMap n x t) r =
      (mappingCone (boundedFlatCoefficientBassSecondSquareComparison P a)).structureMap n
        (Path.toContinuousMap x r) t := rfl

end Quillen.PerfectComplexes
