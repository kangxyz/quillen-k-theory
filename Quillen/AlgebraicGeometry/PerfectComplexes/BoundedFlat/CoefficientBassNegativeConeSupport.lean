/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveSupport

/-! The literal inverse-chart cone inclusion preserves every original cylinder height. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.LoopPrespectrum CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients Quillen.Waldhausen.IteratedS
universe u v
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- The actual strict negative-chart square, with the original inr and identity target map. -/
def boundedFlatCoefficientBassNegativeConeSquare :
    Arrow.mk (boundedFlatPerfectPrespectrumMap (laurentMinus P a)) ⟶
      Arrow.mk (boundedFlatCoefficientBassSquareComparison P a) :=
  Arrow.homMk
    (HomotopyPushout.inr
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))) (𝟙 _)
    (by simpa only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom, Category.comp_id,
      boundedFlatCoefficientBassSquareComparison] using
      (HomotopyPushout.inr_desc
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (laurentPlus P a))
        (boundedFlatPerfectPrespectrumMap (laurentMinus P a))
        (boundedFlatCoefficientBassSquareHomotopy P a)))

/-- The negative subcone enters the original Bass cone by its literal strict square map. -/
def boundedFlatCoefficientBassNegativeConeInclusion :
    mappingCone (boundedFlatPerfectPrespectrumMap (laurentMinus P a)) ⟶
      mappingCone (boundedFlatCoefficientBassSquareComparison P a) :=
  mappingConeMap (boundedFlatCoefficientBassNegativeConeSquare P a)

/-- The target inclusion remains the same Laurent inclusion, with no extra homotopy segment. -/
theorem boundedFlatCoefficientBassNegativeConeInclusion_inclusion :
    mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentMinus P a)) ≫
      boundedFlatCoefficientBassNegativeConeInclusion P a =
        mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a) := by
  apply Hom.ext
  funext n
  ext x
  rfl

/-- Every negative-cone cylinder point retains its own time and actual polynomial-chart point. -/
theorem boundedFlatCoefficientBassNegativeConeInclusion_cylinder (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    (boundedFlatCoefficientBassNegativeConeInclusion P a).map n
      (ReducedMappingCone.cylinder _ _
        ((boundedFlatPerfectPrespectrumMap (laurentMinus P a)).map n) (s, x)) =
      ReducedMappingCone.cylinder _ _ ((boundedFlatCoefficientBassSquareComparison P a).map n)
        (s, (HomotopyPushout.inr
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x) := rfl

end Quillen.PerfectComplexes
