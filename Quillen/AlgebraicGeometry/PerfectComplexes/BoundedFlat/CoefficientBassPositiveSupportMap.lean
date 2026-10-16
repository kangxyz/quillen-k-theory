/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveSupport

/-!
# Actual coefficient maps on the positive cone support

The original polynomial and Laurent coefficient maps and the original positive chart homotopy
induce a map of positive cones. Its strict image in the original two-chart cone is the existing
coefficient cone map, on every inclusion and cylinder point with the original time subdivision.
This support factorization supplies neither a different initial-seed naturality track nor a
mixed C0/J0/C1 filler.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.LoopPrespectrum CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (u : a ⟶ b)

/-- The unchanged positive chart comparison followed by the actual target positive-cone null. -/
def boundedFlatCoefficientBassPositiveConeMapNull :=
  mappingConeSquareNullHomotopy
    (boundedFlatPerfectPrespectrumMap (laurentPlus P a))
    (boundedFlatPerfectPrespectrumMap (laurentPlus P b))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map u)))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map u)))
    (boundedFlatCoefficientPlusSquareHomotopy P u)

/-- The actual coefficient map of positive cones uses the original positive chart square. -/
def boundedFlatCoefficientBassPositiveConeMap :
    mappingCone (boundedFlatPerfectPrespectrumMap (laurentPlus P a)) ⟶
      mappingCone (boundedFlatPerfectPrespectrumMap (laurentPlus P b)) :=
  mappingConeSquareMap
    (boundedFlatPerfectPrespectrumMap (laurentPlus P a))
    (boundedFlatPerfectPrespectrumMap (laurentPlus P b))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map u)))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map u)))
    (boundedFlatCoefficientPlusSquareHomotopy P u)

/-- The Laurent inclusion uses exactly the original Laurent coefficient map. -/
theorem boundedFlatCoefficientBassPositiveConeMap_inclusion :
    mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P a)) ≫
      boundedFlatCoefficientBassPositiveConeMap P u =
    boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map u)) ≫
      mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P b)) :=
  mappingConeSquareMap_inclusion _ _ _ _ _

/-- The complete positive cylinder retains both original halves of the comparison/null track. -/
theorem boundedFlatCoefficientBassPositiveConeMap_cylinder (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    (boundedFlatCoefficientBassPositiveConeMap P u).map n
      (ReducedMappingCone.cylinder _ _
        ((boundedFlatPerfectPrespectrumMap (laurentPlus P a)).map n) (s, x)) =
      (boundedFlatCoefficientBassPositiveConeMapNull P u).level n (s, x) := rfl

/-- Postcomposition of the entire positive null gives the original full cone-map null on inl.
The positive comparison and the target cone cylinder keep their actual separate time halves. -/
theorem boundedFlatCoefficientBassPositiveConeMapNull_factor (n : ℕ) :
    ((boundedFlatCoefficientBassPositiveConeMapNull P u).postcomp
      (boundedFlatCoefficientBassPositiveConeInclusion P b)).level n =
    (Homotopy.precomp
      (HomotopyPushout.inl
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)))
      (mappingConeSquareNullHomotopy
        (boundedFlatCoefficientBassSquareComparison P a)
        (boundedFlatCoefficientBassSquareComparison P b)
        (boundedFlatCoefficientPolynomialSpanMap P u)
        (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map u)))
        (boundedFlatCoefficientBassComparisonHomotopy P u))).level n := by
  simp only [boundedFlatCoefficientBassPositiveConeMapNull, mappingConeSquareNullHomotopy,
    Homotopy.postcomp_trans, Homotopy.precomp_trans]
  apply Homotopy.trans_level_congr <;> rfl

/-- The actual positive cone map factors the existing coefficient cone map literally,
including every original cone-cylinder point. -/
theorem boundedFlatCoefficientBassPositiveConeMap_factor :
    boundedFlatCoefficientBassPositiveConeInclusion P a ≫
      boundedFlatCoefficientBassConeMap P u =
    boundedFlatCoefficientBassPositiveConeMap P u ≫
      boundedFlatCoefficientBassPositiveConeInclusion P b := by
  apply mappingCone_hom_ext
  · apply Hom.ext
    funext n
    ext x
    rfl
  · intro n s x
    exact (DFunLike.congr_fun
      (boundedFlatCoefficientBassPositiveConeMapNull_factor P u n) (s, x)).symm

/-- Parameter looping preserves the literal support factorization and the independent loop time. -/
theorem boundedFlatCoefficientBassPositiveConeMap_loop_factor :
    parameterLoopingMap (boundedFlatCoefficientBassPositiveConeInclusion P a) ≫
      boundedFlatCoefficientBassStepMap P u =
    parameterLoopingMap (boundedFlatCoefficientBassPositiveConeMap P u) ≫
      parameterLoopingMap (boundedFlatCoefficientBassPositiveConeInclusion P b) := by
  change parameterLoopingFunctor.map (boundedFlatCoefficientBassPositiveConeInclusion P a) ≫
      parameterLoopingFunctor.map (boundedFlatCoefficientBassConeMap P u) =
    parameterLoopingFunctor.map (boundedFlatCoefficientBassPositiveConeMap P u) ≫
      parameterLoopingFunctor.map (boundedFlatCoefficientBassPositiveConeInclusion P b)
  rw [← parameterLoopingFunctor.map_comp, ← parameterLoopingFunctor.map_comp]
  exact congrArg parameterLoopingFunctor.map
    (boundedFlatCoefficientBassPositiveConeMap_factor P u)

end Quillen.PerfectComplexes
