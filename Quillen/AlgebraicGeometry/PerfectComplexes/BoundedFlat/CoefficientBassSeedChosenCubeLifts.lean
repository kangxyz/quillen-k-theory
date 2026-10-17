/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedCarrierAugmentationCells
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveActualMixedFiller
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassNegativeActualMixedFiller

/-! Both original chosen cubes enter one actual carrier; their shared J0 surface agrees exactly. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedChosenCubeLifts
open CommonReferenceNerve
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- The original polynomial coefficient inclusion at `a` used by both selected cube lifts. -/
abbrev p := (polynomialUnderCoefficient R).app a
/-- The original inverse Laurent chart at `a` used by both selected cube lifts. -/
abbrev q := (underToLaurentInvert R).app a
/-- The common augmented carrier for the fixed polynomial coefficient inclusion and inverse
Laurent chart. -/
abbrev space := CoefficientBassSeedCarrierAugmentation.space P (p a) (q a)

/-- The old positive cube is transported as a whole, without choosing any new extension. -/
def positiveMap : C(CoefficientBassPositiveC0CarrierSeed.Carrier P
    (p a) ((underToLaurent R).app a), space P a) :=
  (CoefficientBassSeedCarrierAugmentation.originalMap P (p a) (q a)).comp
    (CoefficientBassNegativeActualRightRoute.transport P a)

/-- The negative cube enters through its literal original carrier. -/
def negativeMap := CoefficientBassSeedCarrierAugmentation.originalMap P (p a) (q a)

/-- This is the original positive chosen cube, followed by its displayed map. -/
def positiveCube : C((I × I) × I, space P a) :=
  (positiveMap P a).comp (CoefficientBassPositiveActualMixedFiller.boundary P a).carrier

/-- This is the original negative chosen cube, with the same three original coordinates. -/
def negativeCube : C((I × I) × I, space P a) :=
  (negativeMap P a).comp (CoefficientBassNegativeActualMixedFiller.boundary P a).carrier

/-- Every positive boundary face is preserved at its exact cube coordinates. -/
theorem positive_face (i : Fin 3 × Bool) (z : Quillen.SimplexCubeExtension.face i) :
    positiveMap P a ((CoefficientBassPositiveActualMixedFiller.boundary P a).extension z.val.val) =
      positiveMap P a ((CoefficientBassPositiveActualMixedFiller.boundary P a).faces i z) :=
  congrArg (positiveMap P a)
    ((CoefficientBassPositiveActualMixedFiller.boundary P a).extension_face i z)

/-- Every negative boundary face is preserved, independently of the positive interior. -/
theorem negative_face (i : Fin 3 × Bool) (z : Quillen.SimplexCubeExtension.face i) :
    negativeMap P a ((CoefficientBassNegativeActualMixedFiller.boundary P a).extension z.val.val) =
      negativeMap P a ((CoefficientBassNegativeActualMixedFiller.boundary P a).faces i z) :=
  congrArg (negativeMap P a)
    ((CoefficientBassNegativeActualMixedFiller.boundary P a).extension_face i z)

/-- The common full J0 surface agrees before native evaluation, at both original clocks. -/
theorem shared_j0 (r s : I) :
    positiveMap P a (CoefficientBassPositiveJ0Conjugation.reverseComparison P a (r, s)) =
      negativeMap P a (CoefficientBassNegativeActualRightRoute.j0 P a (r, s)) :=
  (congrArg (negativeMap P a)
    (CoefficientBassNegativeActualRightRoute.j0_apply P a r s)).symm

end Quillen.PerfectComplexes.CoefficientBassSeedChosenCubeLifts
