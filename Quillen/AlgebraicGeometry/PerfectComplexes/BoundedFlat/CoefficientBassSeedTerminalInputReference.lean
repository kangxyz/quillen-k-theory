/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedCarrierLaurentReference
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.DoubleSquareCommonSimplex
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveWhiskered

/-! The full input-reference transport between the two original coefficient seed squares. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedTerminalInputReference
open BassMWholeNerve
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
  (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)

/-- The original source seed input followed by the Laurent coefficient map. -/
abbrev sourceReference :=
  CoefficientBassSeedCarrierLaurentReference.inputReference P
    ((polynomialUnderCoefficient R).app a) (α.app a) ≫
      coefficientModel P ((laurentUnderFunctor R).map f)

/-- The original target seed input, precomposed by the source coefficient map. -/
abbrev targetReference := coefficientModel P f ≫
  CoefficientBassSeedCarrierLaurentReference.inputReference P
    ((polynomialUnderCoefficient R).app b) (α.app b)

/-- The two actual naturality squares and the original triple normalizations,
with every association and equality transport retained. -/
def inputIso : (sourceReference P f α).functor ≅ (targetReference P f α).functor :=
  (NormalizedTripleSimplex.leftFirst
    (coefficientMap P ((laurentUnderFunctor R).map f))
    (coefficientMap P (α.app a))
    (coefficientMap P ((polynomialUnderCoefficient R).app a))).symm ≪≫
  DoubleSquareCommonSimplex.lastSourceIso
    (coefficientMap P ((polynomialUnderCoefficient R).app a))
    (coefficientMap P (α.app a))
    (coefficientMap P ((polynomialUnderCoefficient R).app b))
    (coefficientMap P (α.app b))
    (coefficientMap P f)
    (coefficientMap P ((polynomialUnderFunctor R).map f))
    (coefficientMap P ((laurentUnderFunctor R).map f))
    (coefficientMap_naturality P (polynomialUnderCoefficient R) f)
    (coefficientMap_naturality P α f) ≪≫
  NormalizedTripleSimplex.rightFirst (coefficientMap P (α.app b))
    (coefficientMap P ((polynomialUnderCoefficient R).app b)) (coefficientMap P f)

/-- Every target-input node is placed in the source-input reference with its full anchor. -/
def nodeMap : CommonReferenceNerve.Node (targetReference P f α) →
    CommonReferenceNerve.Node (sourceReference P f α) :=
  CommonReferenceProduct.reanchor (inputIso P f α)

/-- Reference transport leaves the actual functor of each node unchanged. -/
theorem nodeMap_functor (N : CommonReferenceNerve.Node (targetReference P f α)) :
    (nodeMap P f α N).1 = N.1 := rfl

/-- The entire target-input nerve is transported with the original normalization word. -/
def parameterMap := CommonReferenceNerve.mapParameter (nodeMap P f α)

/-- Every level and every genuine source input is preserved by the full reference transport. -/
theorem parameterMap_native (n : ℕ)
    (y : |nerve (Codiscrete (CommonReferenceNerve.Node (targetReference P f α)))|)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CommonReferenceNerve.pointwisePrespectrumFamily (sourceReference P f α) n
        (parameterMap P f α y) x =
      CommonReferenceNerve.pointwisePrespectrumFamily (targetReference P f α) n y x :=
  CommonReferenceNerve.pointwise_reanchor (inputIso P f α) n y x

end Quillen.PerfectComplexes.CoefficientBassSeedTerminalInputReference
