/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCutOpenPrecompMap
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedChosenCubeLifts

/-! Actual coefficient-source precomposition of both previously chosen comparison cubes. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedCoefficientPrecomp
open CommonReferenceNerve CoefficientBassPositiveC1BoundaryLift
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)

/-- The normalized coefficient model map associated with `f`. -/
abbrev inputMap := BassH0Merge.normalizedMap (coefficientMap P f)
/-- The polynomial seed reference for the coefficient at `b` and the inverted Laurent chart. -/
abbrev polyRef := polynomialReference P ((polynomialUnderCoefficient R).app b)
  ((underToLaurentInvert R).app b)
/-- The Laurent seed reference for the coefficient at `b` and the inverted Laurent chart. -/
abbrev laurentRef := laurentReference P ((polynomialUnderCoefficient R).app b)
  ((underToLaurentInvert R).app b)
/-- The seed chart map at the Laurent coefficient object over `b`. -/
abbrev chart := chartMap P (c := (laurentUnderFunctor R).obj b)
/-- The ordinary seed anchor for the coefficient at `b` and the inverted Laurent chart. -/
abbrev ordinary := ordinaryAnchor P ((polynomialUnderCoefficient R).app b)
  ((underToLaurentInvert R).app b)
/-- The shifted seed anchor for the coefficient at `b` and the inverted Laurent chart. -/
abbrev shifted := LaurentUnitReferenceSpecialization.shiftedAnchor P
  ((polynomialUnderCoefficient R).app b) ((underToLaurentInvert R).app b)

/-- The ordinary seed anchor transported by source precomposition with `inputMap P f`. -/
abbrev ordinaryPre := CutOpenPrecomp.anchor (inputMap P f) (polyRef P (b := b))
  (chart P (b := b)) (laurentRef P (b := b)) (ordinary P (b := b))
/-- The shifted seed anchor transported by source precomposition with `inputMap P f`. -/
abbrev shiftedPre := CutOpenPrecomp.anchor (inputMap P f) (polyRef P (b := b))
  (chart P (b := b)) (laurentRef P (b := b)) (shifted P (b := b))

/-- The source model is now the actual coefficient source a, without identifying it with b. -/
abbrev space := CutOpenCarrier.space (inputMap P f ≫ polyRef P (b := b))
  (chart P (b := b)) (inputMap P f ≫ laurentRef P (b := b))
  (ordinaryPre P f) (shiftedPre P f)

/-- Both complete attachments are preserved by the original source-domain map. -/
def sourceMap : C(CoefficientBassPositiveC0CarrierSeed.Carrier P
    ((polynomialUnderCoefficient R).app b) ((underToLaurentInvert R).app b), space P f) :=
  (CutOpenPrecomp.map (inputMap P f) (polyRef P (b := b)) (chart P (b := b))
    (laurentRef P (b := b)) (ordinary P (b := b)) (shifted P (b := b))).hom

/-- The exact ordinary full-reference square, before geometric realization or evaluation. -/
theorem ordinary_attachment :
    CutOpenCarrier.attaching (polyRef P (b := b)) (chart P (b := b))
        (laurentRef P (b := b)) (ordinary P (b := b)) ≫
      nerveMap (Codiscrete.functorOfFun (precompNode (inputMap P f))) =
    nerveMap (Codiscrete.functorOfFun (precompNode (inputMap P f))) ≫
      CutOpenCarrier.attaching (inputMap P f ≫ polyRef P (b := b))
        (chart P (b := b)) (inputMap P f ≫ laurentRef P (b := b)) (ordinaryPre P f) :=
  CutOpenPrecomp.attachment_simplicial _ _ _ _ _

/-- The shifted square retains the actual forward inner-unit reference in full. -/
theorem shifted_attachment :
    CutOpenCarrier.attaching (polyRef P (b := b)) (chart P (b := b))
        (laurentRef P (b := b)) (shifted P (b := b)) ≫
      nerveMap (Codiscrete.functorOfFun (precompNode (inputMap P f))) =
    nerveMap (Codiscrete.functorOfFun (precompNode (inputMap P f))) ≫
      CutOpenCarrier.attaching (inputMap P f ≫ polyRef P (b := b))
        (chart P (b := b)) (inputMap P f ≫ laurentRef P (b := b)) (shiftedPre P f) :=
  CutOpenPrecomp.attachment_simplicial _ _ _ _ _

/-- The two old selected interiors are composed separately with the same source-domain map. -/
def positiveCube : C((I × I) × I, space P f) :=
  (sourceMap P f).comp ((CoefficientBassNegativeActualRightRoute.transport P b).comp
    (CoefficientBassPositiveActualMixedFiller.boundary P b).carrier)

/-- The negative mixed-filler cube transported through the source coefficient map. -/
def negativeCube : C((I × I) × I, space P f) :=
  (sourceMap P f).comp (CoefficientBassNegativeActualMixedFiller.boundary P b).carrier

/-- Their shared J0 surface agrees as a whole scalar surface after source precomposition. -/
theorem shared_j0 (r s : I) :
    sourceMap P f (CoefficientBassNegativeActualRightRoute.transport P b
      (CoefficientBassPositiveJ0Conjugation.reverseComparison P b (r, s))) =
    sourceMap P f (CoefficientBassNegativeActualRightRoute.j0 P b (r, s)) :=
  (congrArg (sourceMap P f)
    (CoefficientBassNegativeActualRightRoute.j0_apply P b r s)).symm

end Quillen.PerfectComplexes.CoefficientBassSeedCoefficientPrecomp
