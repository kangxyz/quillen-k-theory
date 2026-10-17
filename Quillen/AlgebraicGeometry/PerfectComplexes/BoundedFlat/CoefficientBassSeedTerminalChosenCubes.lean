/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTerminalCarrierMap
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedChosenCubeLifts

/-! Transport the unchanged chosen target cubes through genuine input and reference maps. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedTerminalChosenCubes
open CoefficientBassSeedTerminalCarrierMap
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)

/-- The positive chosen carrier first uses its original full negative-reference transport. -/
def positiveMap : C(CoefficientBassPositiveC0CarrierSeed.Carrier P
    ((polynomialUnderCoefficient R).app b) ((underToLaurent R).app b),
      targetCarrier P f (underToLaurentInvert R)) :=
  ⟨fun y ↦ carrierMap P f (underToLaurentInvert R)
    (CoefficientBassNegativeActualRightRoute.transport P b y),
    (carrierMap P f (underToLaurentInvert R)).continuous.comp
      (CoefficientBassNegativeActualRightRoute.transport P b).continuous⟩

/-- The positive target cube is the original chosen cube with its original three coordinates. -/
def positiveCube : C((I × I) × I, targetCarrier P f (underToLaurentInvert R)) :=
  (positiveMap P f).comp
    (CoefficientBassPositiveActualMixedFiller.boundary P b).carrier

/-- The negative target cube is independently the original chosen cube, without reselection. -/
def negativeCube : C((I × I) × I, targetCarrier P f (underToLaurentInvert R)) :=
  (carrierMap P f (underToLaurentInvert R)).comp
    (CoefficientBassNegativeActualMixedFiller.boundary P b).carrier

/-- Every original positive face is retained at its literal extension coordinates. -/
theorem positive_face (i : Fin 3 × Bool) (z : Quillen.SimplexCubeExtension.face i) :
    positiveMap P f
      ((CoefficientBassPositiveActualMixedFiller.boundary P b).extension z.val.val) =
    positiveMap P f
      ((CoefficientBassPositiveActualMixedFiller.boundary P b).faces i z) :=
  congrArg (positiveMap P f)
    ((CoefficientBassPositiveActualMixedFiller.boundary P b).extension_face i z)

/-- Every original negative face is retained independently of the positive interior. -/
theorem negative_face (i : Fin 3 × Bool) (z : Quillen.SimplexCubeExtension.face i) :
    carrierMap P f (underToLaurentInvert R)
      ((CoefficientBassNegativeActualMixedFiller.boundary P b).extension z.val.val) =
    carrierMap P f (underToLaurentInvert R)
      ((CoefficientBassNegativeActualMixedFiller.boundary P b).faces i z) :=
  congrArg (carrierMap P f (underToLaurentInvert R))
    ((CoefficientBassNegativeActualMixedFiller.boundary P b).extension_face i z)

private theorem post_j0 {X : Type*}
    (g : CoefficientBassPositiveC0CarrierSeed.Carrier P
      ((polynomialUnderCoefficient R).app b) ((underToLaurentInvert R).app b) → X)
    (r s : I) :
    g (CoefficientBassNegativeActualRightRoute.transport P b
      (CoefficientBassPositiveJ0Conjugation.reverseComparison P b (r, s))) =
      g (CoefficientBassNegativeActualRightRoute.j0 P b (r, s)) :=
  (congrArg g (CoefficientBassNegativeActualRightRoute.j0_apply P b r s)).symm

/-- The shared original J0 surface agrees before evaluation, at both unchanged clocks. -/
theorem shared_j0 (r s : I) :
    positiveMap P f (CoefficientBassPositiveJ0Conjugation.reverseComparison P b (r, s)) =
      carrierMap P f (underToLaurentInvert R)
        (CoefficientBassNegativeActualRightRoute.j0 P b (r, s)) := by
  dsimp only [positiveMap, ContinuousMap.comp_apply]
  exact post_j0 P (carrierMap P f (underToLaurentInvert R)) r s

end Quillen.PerfectComplexes.CoefficientBassSeedTerminalChosenCubes
