/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSectionEvaluationBassSeed
public import Quillen.Topology.Prespectrum.SelfTrackStableNullEvaluation

/-!
# Stable factorization of the original raw native Bass transition

The original forward Laurent self-track, original positive source null and original cone
inclusion identify the actual raw transition in every integer degree. The exact parameter-loop
shift retains its alternating stage sign and negative-degree tail. This does not compare the
cone to supported K-theory or assert an all-degree Laurent boundary splitting.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- The original transition factors through the actual Laurent self-track and cone inclusion. -/
theorem boundedFlatCoefficientBassTransition_stableHomotopy (d : ℤ) :
    (stableHomotopyFunctor d).map (boundedFlatCoefficientBassTransition P a) ≫
        (parameterStableHomotopyIso
          (mappingCone (boundedFlatCoefficientBassSquareComparison P a)) d).hom =
      (boundedFlatCoefficientLaurentUnitHomotopy P a).stableOperation d ≫
        (stableHomotopyFunctor (d + 1)).map
          (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)) :=
  (boundedFlatCoefficientLaurentUnitHomotopy P a).nullLoopMap_stableHomotopy_postcomp
    (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))
    (boundedFlatCoefficientBassLaurentNullHomotopy P a) d

/-- Solving for the unchanged raw seed uses the same exact parameter-loop shift inverse. -/
theorem boundedFlatCoefficientBassTransition_stableHomotopy_eq (d : ℤ) :
    (stableHomotopyFunctor d).map (boundedFlatCoefficientBassTransition P a) =
      (boundedFlatCoefficientLaurentUnitHomotopy P a).stableOperation d ≫
        (stableHomotopyFunctor (d + 1)).map
          (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)) ≫
            (parameterStableHomotopyIso
              (mappingCone (boundedFlatCoefficientBassSquareComparison P a)) d).inv := by
  apply (cancel_mono (parameterStableHomotopyIso
    (mappingCone (boundedFlatCoefficientBassSquareComparison P a)) d).hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    boundedFlatCoefficientBassTransition_stableHomotopy P a d

/-- Every original source stage retains the exact sign, Laurent target stage and integer tail. -/
theorem boundedFlatCoefficientBassTransition_stableHomotopy_ι (d : ℤ) (n : ℕ) :
    stableHomotopyι
        (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))) d n ≫
      (stableHomotopyFunctor d).map (boundedFlatCoefficientBassTransition P a) ≫
        (parameterStableHomotopyIso
          (mappingCone (boundedFlatCoefficientBassSquareComparison P a)) d).hom =
      ((-1 : ℤ) ^ n •
        (boundedFlatCoefficientLaurentUnitHomotopy P a).stableStageOperation d n) ≫
        (shiftedStableReindexIso (originalPrespectrum (boundedFlatPerfectWaldhausen
          (space (op P, (laurentUnderFunctor R).obj a)))) d n).hom ≫
          stableHomotopyι (originalPrespectrum (boundedFlatPerfectWaldhausen
            (space (op P, (laurentUnderFunctor R).obj a)))) (d + 1)
              (parameterStableOffset d + n) ≫
            (stableHomotopyFunctor (d + 1)).map
              (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)) := by
  rw [boundedFlatCoefficientBassTransition_stableHomotopy, ← Category.assoc,
    Homotopy.stableOperation_ι]
  simp only [Category.assoc]

/-- The original null-conjugated seed also keeps its actual finite level, including level zero. -/
theorem boundedFlatCoefficientBassTransition_piMap (n m : ℕ)
    (x : HomotopyGroup.Pi (m + 1)
      ((originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n)
      ((originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).point n)) :
    (loopShiftMulEquiv
      (x := (mappingCone (boundedFlatCoefficientBassSquareComparison P a)).point n) m).symm
        (piMap m ((boundedFlatCoefficientBassTransition P a).map n)
          ((boundedFlatCoefficientBassTransition P a).map_point n) x) =
      Homotopy.homotopyClassOperation
        ((boundedFlatCoefficientLaurentUnitHomotopy P a).postcomp
          (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))) n m x :=
  ((boundedFlatCoefficientLaurentUnitHomotopy P a).postcomp
    (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a))).nullLoopMap_piMap
      (boundedFlatCoefficientBassLaurentNullHomotopy P a) n m x

end Quillen.PerfectComplexes
