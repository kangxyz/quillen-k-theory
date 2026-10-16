/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSecondStep

/-! Named consumers of the actual second object, its fixed chart tracks and positive source null.
These check the literal cone and independent comparison, inner-loop, outer-loop and structure
coordinates, including level zero. No second coefficient map or tower transition is assumed. -/
@[expose] public section
noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen Quillen.LoopPrespectrum Quillen.PerfectComplexes CommRingCat.PolynomialLaurent
universe u
namespace QuillenTest.CoefficientBassSecondStep
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- The fixed positive chart begins at the original first-step Laurent coefficient cone map. -/
theorem positive_source_endpoint (n : ℕ) (s : unitInterval)
    (x : (boundedFlatCoefficientBassStep P a).space n) :
    Path.toContinuousMap
      ((boundedFlatCoefficientBassSecondPlusHomotopy P a).level n (0, x)) s =
      (boundedFlatCoefficientBassConeMap P ((laurentUnderCoefficient R).app a)).map n
        (Path.toContinuousMap x s) :=
  congrArg (fun p ↦ Path.toContinuousMap p s)
    ((boundedFlatCoefficientBassSecondPlusHomotopy P a).at_zero n x)

/-- The inverse chart ends at the actual two original coefficient cone maps in order. -/
theorem inverse_target_endpoint (n : ℕ) (s : unitInterval)
    (x : (boundedFlatCoefficientBassStep P a).space n) :
    Path.toContinuousMap
      ((boundedFlatCoefficientBassSecondMinusHomotopy P a).level n (1, x)) s =
      (boundedFlatCoefficientBassConeMap P ((underToLaurentInvert R).app a)).map n
        ((boundedFlatCoefficientBassConeMap P ((polynomialUnderCoefficient R).app a)).map n
          (Path.toContinuousMap x s)) :=
  congrArg (fun p ↦ Path.toContinuousMap p s)
    ((boundedFlatCoefficientBassSecondMinusHomotopy P a).at_one n x)

/-- The whole fixed positive cube remains visible on the original level-zero loop space. -/
theorem positive_level_zero (r s : unitInterval)
    (x : (boundedFlatCoefficientBassStep P a).space 0) :
    Path.toContinuousMap
      ((boundedFlatCoefficientBassSecondPlusHomotopy P a).level 0 (r, x)) s =
      (BassMWhole.coneComposition P ((polynomialUnderCoefficient R).app a)
        ((underToLaurent R).app a)).level 0 (r, Path.toContinuousMap x s) :=
  boundedFlatCoefficientBassSecondPlusHomotopy_apply P a 0 r s x

/-- Inverse comparison, inner loop and structure times are three independent parameters. -/
theorem inverse_independent_structure_time (n : ℕ) (r s t : unitInterval)
    (x : (boundedFlatCoefficientBassStep P a).space n) :
    Path.toContinuousMap
      ((boundedFlatCoefficientBassSecondMinusHomotopy P a).level (n + 1)
        (r, (boundedFlatCoefficientBassStep P a).structureMap n x t)) s =
      (mappingCone (boundedFlatCoefficientBassSquareComparison P
        ((laurentUnderFunctor R).obj a))).structureMap n
          ((BassMWhole.coneComposition P ((polynomialUnderCoefficient R).app a)
            ((underToLaurentInvert R).app a)).level n (r, Path.toContinuousMap x s)) t :=
  congrArg (fun p ↦ Path.toContinuousMap p s)
    ((boundedFlatCoefficientBassSecondMinusHomotopy P a).comm n r x t)

/-- The entire original overlap remains unchanged after entering the literal second cone. -/
theorem whole_overlap_inside_cone (n : ℕ) (r : unitInterval)
    (x : (boundedFlatCoefficientBassStep P a).space n) :
    (boundedFlatCoefficientBassSecondConeInclusion P a).map n
      ((boundedFlatCoefficientBassSecondSquareComparison P a).map n
        (HomotopyPushout.cylinder
          (boundedFlatCoefficientBassStepMap P ((polynomialUnderCoefficient R).app a))
          (boundedFlatCoefficientBassStepMap P ((polynomialUnderCoefficient R).app a)) n (r, x))) =
      (boundedFlatCoefficientBassSecondConeInclusion P a).map n
        ((boundedFlatCoefficientBassSecondPlusHomotopy P a).symm.trans
          (boundedFlatCoefficientBassSecondMinusHomotopy P a) |>.level n (r, x)) := rfl

/-- The canonical positive null starts at the original Laurent source map and literal inclusion. -/
theorem positive_null_source (n : ℕ)
    (x : (boundedFlatCoefficientBassStep P a).space n) :
    (boundedFlatCoefficientBassSecondLaurentNullHomotopy P a).level n (0, x) =
      (boundedFlatCoefficientBassSecondConeInclusion P a).map n
        ((boundedFlatCoefficientBassStepMap P ((laurentUnderCoefficient R).app a)).map n x) :=
  (boundedFlatCoefficientBassSecondLaurentNullHomotopy P a).at_zero n x

/-- The same null ends at the actual second comparison cone's based point, also in degree zero. -/
theorem positive_null_target_zero
    (x : (boundedFlatCoefficientBassStep P a).space 0) :
    (boundedFlatCoefficientBassSecondLaurentNullHomotopy P a).level 0 (1, x) =
      (mappingCone (boundedFlatCoefficientBassSecondSquareComparison P a)).point 0 :=
  (boundedFlatCoefficientBassSecondLaurentNullHomotopy P a).at_one 0 x

/-- Null time and the original source structure time are independent on the entire native loop. -/
theorem positive_null_structure (n : ℕ) (r t : unitInterval)
    (x : (boundedFlatCoefficientBassStep P a).space n) :
    (boundedFlatCoefficientBassSecondLaurentNullHomotopy P a).level (n + 1)
        (r, (boundedFlatCoefficientBassStep P a).structureMap n x t) =
      (mappingCone (boundedFlatCoefficientBassSecondSquareComparison P a)).structureMap n
        ((boundedFlatCoefficientBassSecondLaurentNullHomotopy P a).level n (r, x)) t :=
  (boundedFlatCoefficientBassSecondLaurentNullHomotopy P a).comm n r x t

/-- The literal cone cylinder retains its own time while the whole pushout point is arbitrary. -/
theorem actual_cone_cylinder (n : ℕ) (r : unitInterval)
    (x : (HomotopyPushout.prespectrum
      (boundedFlatCoefficientBassStepMap P ((polynomialUnderCoefficient R).app a))
      (boundedFlatCoefficientBassStepMap P ((polynomialUnderCoefficient R).app a))).space n) :
    (mappingConeHomotopy (boundedFlatCoefficientBassSecondSquareComparison P a)).level n (r, x) =
      ReducedMappingCone.cylinder _ _
        ((boundedFlatCoefficientBassSecondSquareComparison P a).map n) (r, x) := rfl

/-- The outer looped inclusion keeps its actual double-looped Laurent input in degree zero. -/
theorem outer_looped_inclusion_zero (r : unitInterval)
    (x : (parameterLooping
      (boundedFlatCoefficientBassStep P ((laurentUnderFunctor R).obj a))).space 0) :
    Path.toContinuousMap ((boundedFlatCoefficientBassSecondLoopedInclusion P a).map 0 x) r =
      ReducedMappingCone.inr _ _
        ((boundedFlatCoefficientBassSecondSquareComparison P a).map 0)
        (Path.toContinuousMap x r) := rfl

/-- The second object's structure transpose keeps outer-loop and structure coordinates separate. -/
theorem outer_loop_structure_zero (r t : unitInterval)
    (x : (boundedFlatCoefficientBassSecondStep P a).space 0) :
    Path.toContinuousMap ((boundedFlatCoefficientBassSecondStep P a).structureMap 0 x t) r =
      (mappingCone (boundedFlatCoefficientBassSecondSquareComparison P a)).structureMap 0
        (Path.toContinuousMap x r) t :=
  boundedFlatCoefficientBassSecondStep_structure P a 0 r t x

/-- The original positive null is based throughout its whole time coordinate. -/
theorem positive_null_based (n : ℕ) (r : unitInterval) :
    (boundedFlatCoefficientBassSecondLaurentNullHomotopy P a).level n
      (r, (boundedFlatCoefficientBassStep P a).point n) =
      (mappingCone (boundedFlatCoefficientBassSecondSquareComparison P a)).point n :=
  (boundedFlatCoefficientBassSecondLaurentNullHomotopy P a).at_point n r

end QuillenTest.CoefficientBassSecondStep
