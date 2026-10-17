/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassNegativeConeSupport

/-!
# Actual coefficient maps on the negative cone support

The original polynomial and Laurent coefficient maps and the original negative chart homotopy
induce a map of negative cones. Its strict image in the original two-chart cone is the existing
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

/-- The unchanged negative chart comparison followed by the actual target negative-cone null. -/
def boundedFlatCoefficientBassNegativeConeMapNull :=
  mappingConeSquareNullHomotopy
    (boundedFlatPerfectPrespectrumMap (laurentMinus P a))
    (boundedFlatPerfectPrespectrumMap (laurentMinus P b))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map u)))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map u)))
    (boundedFlatCoefficientMinusSquareHomotopy P u)

/-- The actual coefficient map of negative cones uses the original negative chart square. -/
def boundedFlatCoefficientBassNegativeConeMap :
    mappingCone (boundedFlatPerfectPrespectrumMap (laurentMinus P a)) ⟶
      mappingCone (boundedFlatPerfectPrespectrumMap (laurentMinus P b)) :=
  mappingConeSquareMap
    (boundedFlatPerfectPrespectrumMap (laurentMinus P a))
    (boundedFlatPerfectPrespectrumMap (laurentMinus P b))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map u)))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map u)))
    (boundedFlatCoefficientMinusSquareHomotopy P u)

/-- The Laurent inclusion uses exactly the original Laurent coefficient map. -/
theorem boundedFlatCoefficientBassNegativeConeMap_inclusion :
    mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentMinus P a)) ≫
      boundedFlatCoefficientBassNegativeConeMap P u =
    boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map u)) ≫
      mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentMinus P b)) :=
  mappingConeSquareMap_inclusion _ _ _ _ _

/-- The complete negative cylinder retains both original halves of the comparison/null track. -/
theorem boundedFlatCoefficientBassNegativeConeMap_cylinder (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    (boundedFlatCoefficientBassNegativeConeMap P u).map n
      (ReducedMappingCone.cylinder _ _
        ((boundedFlatPerfectPrespectrumMap (laurentMinus P a)).map n) (s, x)) =
      (boundedFlatCoefficientBassNegativeConeMapNull P u).level n (s, x) := rfl

/-- Postcomposition of the entire negative null gives the original full cone-map null on inr.
The negative comparison and the target cone cylinder keep their actual separate time halves. -/
theorem boundedFlatCoefficientBassNegativeConeMapNull_factor (n : ℕ) :
    ((boundedFlatCoefficientBassNegativeConeMapNull P u).postcomp
      (boundedFlatCoefficientBassNegativeConeInclusion P b)).level n =
    (Homotopy.precomp
      (HomotopyPushout.inr
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)))
      (mappingConeSquareNullHomotopy
        (boundedFlatCoefficientBassSquareComparison P a)
        (boundedFlatCoefficientBassSquareComparison P b)
        (boundedFlatCoefficientPolynomialSpanMap P u)
        (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map u)))
        (boundedFlatCoefficientBassComparisonHomotopy P u))).level n := by
  simp only [boundedFlatCoefficientBassNegativeConeMapNull, mappingConeSquareNullHomotopy,
    Homotopy.postcomp_trans, Homotopy.precomp_trans]
  apply Homotopy.trans_level_congr <;> rfl

/-- The actual negative cone map factors the existing coefficient cone map literally,
including every original cone-cylinder point. -/
theorem boundedFlatCoefficientBassNegativeConeMap_factor :
    boundedFlatCoefficientBassNegativeConeInclusion P a ≫
      boundedFlatCoefficientBassConeMap P u =
    boundedFlatCoefficientBassNegativeConeMap P u ≫
      boundedFlatCoefficientBassNegativeConeInclusion P b := by
  apply mappingCone_hom_ext
  · apply Hom.ext
    funext n
    ext x
    rfl
  · intro n s x
    exact (DFunLike.congr_fun
      (boundedFlatCoefficientBassNegativeConeMapNull_factor P u n) (s, x)).symm

/-- Parameter looping preserves the literal support factorization and the independent loop time. -/
theorem boundedFlatCoefficientBassNegativeConeMap_loop_factor :
    parameterLoopingMap (boundedFlatCoefficientBassNegativeConeInclusion P a) ≫
      boundedFlatCoefficientBassStepMap P u =
    parameterLoopingMap (boundedFlatCoefficientBassNegativeConeMap P u) ≫
      parameterLoopingMap (boundedFlatCoefficientBassNegativeConeInclusion P b) := by
  change parameterLoopingFunctor.map (boundedFlatCoefficientBassNegativeConeInclusion P a) ≫
      parameterLoopingFunctor.map (boundedFlatCoefficientBassConeMap P u) =
    parameterLoopingFunctor.map (boundedFlatCoefficientBassNegativeConeMap P u) ≫
      parameterLoopingFunctor.map (boundedFlatCoefficientBassNegativeConeInclusion P b)
  rw [← parameterLoopingFunctor.map_comp, ← parameterLoopingFunctor.map_comp]
  exact congrArg parameterLoopingFunctor.map
    (boundedFlatCoefficientBassNegativeConeMap_factor P u)

end Quillen.PerfectComplexes
