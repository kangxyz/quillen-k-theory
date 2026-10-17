/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTerminalInputReference
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTargetUnitReference

/-! The terminal seed reference retains the source and target Laurent normalizations. -/
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
namespace Quillen.PerfectComplexes.CoefficientBassSeedTerminalLaurentReference
open BassMWholeNerve CommonReferenceNerve
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
  (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)

/-- The actual old Laurent reference after the prescribed coefficient action. -/
abbrev sourceReference :=
  CoefficientBassPositiveC1BoundaryLift.laurentReference P
    ((polynomialUnderCoefficient R).app a) (α.app a) ≫
      coefficientModel P ((laurentUnderFunctor R).map ((laurentUnderFunctor R).map f))

/-- The actual target Laurent reference after source precomposition. -/
abbrev targetReference := coefficientModel P f ≫
  CoefficientBassPositiveC1BoundaryLift.laurentReference P
    ((polynomialUnderCoefficient R).app b) (α.app b)

/-- The complete target reference enters the precomposed original target Laurent reference. -/
def targetIso :
    (BassProjectionPath.WholeReference.reference P ((laurentUnderFunctor R).obj b)
      (CoefficientBassSeedTerminalInputReference.targetReference P f α)).functor ≅
        (targetReference P f α).functor :=
  Functor.associator (coefficientModel P f).functor
    (CoefficientBassSeedCarrierLaurentReference.inputReference P
      ((polynomialUnderCoefficient R).app b) (α.app b)).functor
    (BassProjectionPath.source P ((laurentUnderFunctor R).obj b)).functor ≪≫
  isoWhiskerLeft (coefficientModel P f).functor
    (CoefficientBassSeedCarrierLaurentReference.referenceIso P
      ((polynomialUnderCoefficient R).app b) (α.app b))

/-- Both original normalization routes and the genuine two-square input transport. -/
def referenceIso : (sourceReference P f α).functor ≅ (targetReference P f α).functor :=
  (CoefficientBassSeedTargetReferenceTransport.referenceIso P
    ((laurentUnderFunctor R).map f)
    (CoefficientBassSeedCarrierLaurentReference.inputReference P
      ((polynomialUnderCoefficient R).app a) (α.app a))
    (CoefficientBassPositiveC1BoundaryLift.laurentReference P
      ((polynomialUnderCoefficient R).app a) (α.app a))
    (CoefficientBassSeedCarrierLaurentReference.referenceIso P
      ((polynomialUnderCoefficient R).app a) (α.app a))).symm ≪≫
  isoWhiskerRight (CoefficientBassSeedTerminalInputReference.inputIso P f α)
    (BassProjectionPath.source P ((laurentUnderFunctor R).obj b)).functor ≪≫
  targetIso P f α

/-- The same complete transport intertwines the prescribed inner units on both seed sides. -/
theorem unit_intertwine :
    Quillen.FunctorIdentityAutomorphism.onFunctor (targetReference P f α).functor
        (LaurentUnitReferenceSpecialization.smallUnit P ((laurentUnderFunctor R).obj b)) ≪≫
      (referenceIso P f α).symm =
    (referenceIso P f α).symm ≪≫ isoWhiskerRight
      (Quillen.FunctorIdentityAutomorphism.onFunctor
        (CoefficientBassPositiveC1BoundaryLift.laurentReference P
          ((polynomialUnderCoefficient R).app a) (α.app a)).functor
        (LaurentUnitReferenceSpecialization.smallUnit P ((laurentUnderFunctor R).obj a)))
      (coefficientModel P
        ((laurentUnderFunctor R).map ((laurentUnderFunctor R).map f))).functor :=
  CoefficientBassSeedTargetUnitReference.unit_intertwine P
    ((laurentUnderFunctor R).map f)
    (CoefficientBassPositiveC1BoundaryLift.laurentReference P
      ((polynomialUnderCoefficient R).app a) (α.app a))
    (targetReference P f α) (referenceIso P f α).symm

/-- Whole Laurent nodes, including their complete anchors, share the terminal reference. -/
def nodeMap : Node (targetReference P f α) → Node (sourceReference P f α) :=
  CommonReferenceProduct.reanchor (referenceIso P f α)

/-- The transport applies to the whole parameter nerve. -/
def parameterMap := mapParameter (nodeMap P f α)

/-- Full reference transport preserves every native value on the genuine base input. -/
theorem parameterMap_native (n : ℕ)
    (y : |nerve (Codiscrete (Node (targetReference P f α)))|)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    pointwisePrespectrumFamily (sourceReference P f α) n (parameterMap P f α y) x =
      pointwisePrespectrumFamily (targetReference P f α) n y x :=
  pointwise_reanchor (referenceIso P f α) n y x

end Quillen.PerfectComplexes.CoefficientBassSeedTerminalLaurentReference
