/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassTransitionStable

/-! Strict clients keep the original raw seed, its negative-degree tail and finite level zero. -/
public section
noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients Quillen.PerfectComplexes
universe u
namespace QuillenTest.CoefficientBassTransitionStable
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

theorem original_degree_zero :
    (stableHomotopyFunctor 0).map (boundedFlatCoefficientBassTransition P a) =
      (boundedFlatCoefficientLaurentUnitHomotopy P a).stableOperation 0 ≫
        (stableHomotopyFunctor (0 + 1)).map
          (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)) ≫
            (parameterStableHomotopyIso
              (mappingCone (boundedFlatCoefficientBassSquareComparison P a)) 0).inv :=
  boundedFlatCoefficientBassTransition_stableHomotopy_eq P a 0

theorem original_negative_tail (n : ℕ) :
    stableHomotopyι
        (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))) (-1) n ≫
      (stableHomotopyFunctor (-1)).map (boundedFlatCoefficientBassTransition P a) ≫
        (parameterStableHomotopyIso
          (mappingCone (boundedFlatCoefficientBassSquareComparison P a)) (-1)).hom =
      ((-1 : ℤ) ^ n •
        (boundedFlatCoefficientLaurentUnitHomotopy P a).stableStageOperation (-1) n) ≫
        (shiftedStableReindexIso (originalPrespectrum (boundedFlatPerfectWaldhausen
          (space (op P, (laurentUnderFunctor R).obj a)))) (-1) n).hom ≫
          stableHomotopyι (originalPrespectrum (boundedFlatPerfectWaldhausen
            (space (op P, (laurentUnderFunctor R).obj a)))) ((-1 : ℤ) + 1)
              (parameterStableOffset (-1) + n) ≫
            (stableHomotopyFunctor ((-1 : ℤ) + 1)).map
              (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)) :=
  boundedFlatCoefficientBassTransition_stableHomotopy_ι P a (-1) n

theorem original_negative_tail_offset : parameterStableOffset (-1) = 1 := rfl

theorem original_finite_level_zero
    (x : HomotopyGroup.Pi 1
      ((originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space 0)
      ((originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).point 0)) :
    (loopShiftMulEquiv
      (x := (mappingCone (boundedFlatCoefficientBassSquareComparison P a)).point 0) 0).symm
        (piMap 0 ((boundedFlatCoefficientBassTransition P a).map 0)
          ((boundedFlatCoefficientBassTransition P a).map_point 0) x) =
      Homotopy.homotopyClassOperation
        ((boundedFlatCoefficientLaurentUnitHomotopy P a).postcomp
          (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))) 0 0 x :=
  boundedFlatCoefficientBassTransition_piMap P a 0 0 x

end QuillenTest.CoefficientBassTransitionStable
