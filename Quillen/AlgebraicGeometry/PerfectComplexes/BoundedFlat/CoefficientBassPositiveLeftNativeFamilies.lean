/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftMidpointUnit
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveTransitionNaturality
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveReanchorFamily
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCutOpenEvaluation
public import Quillen.Topology.Prespectrum.RelativeHomotopyEndpointEvaluation

/-! Finite first/middle family evaluation and the original cone-inclusion transports. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Simplicial Topology unitInterval
universe u

namespace Quillen.PerfectComplexes.CoefficientBassPositiveLeftNativeFamilies
open CommonReferenceNerve CoefficientBassPositiveC1BoundaryLift
open CoefficientBassPositiveC0CarrierSeed CoefficientBassPositiveLeftMidpointUnit
variable {R : CommRingCat.{u}} (P : Over (Spec R))

/-- The original positive-pasting endpoint transport does not change either native time. -/
theorem positivePasting_value {a b : Under R} (w : a ⟶ b) (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (CoefficientBassPositiveNullTrack.positivePasting P w).level n (r, (s, x)) =
      (mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P b))).map n
        ((boundedFlatCoefficientPlusPasting P w).level n (r, (s, x))) := by
  unfold CoefficientBassPositiveNullTrack.positivePasting
  apply Homotopy.RelHomotopy.transport_apply
  all_goals simp only [boundedFlatCoefficientPlusLeftTrack, boundedFlatCoefficientPlusRightTrack,
    Homotopy.postcomp_trans, Homotopy.postcomp_symm,
    CoefficientBassPositiveNullTrack.positiveMovement,
    CoefficientBassPositiveNullTrack.polynomialMovement,
    CoefficientBassPositiveNullTrack.oldPositive, CoefficientBassPositiveNullTrack.laurentMovement,
    CoefficientBassPositiveNullTrack.newPositive]

/-- The original unit-pasting endpoint transport retains every comparison and unit time. -/
theorem unitPasting_value {a b : Under R} (w : a ⟶ b) (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (CoefficientBassPositiveTransitionTrack.unitPasting P w).level n (r, (s, x)) =
      (mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P b))).map n
        ((boundedFlatCoefficientLaurentUnitPasting P w).level n (r, (s, x))) := by
  unfold CoefficientBassPositiveTransitionTrack.unitPasting
  apply Homotopy.RelHomotopy.transport_apply
  all_goals simp only [Homotopy.postcomp_trans,
    CoefficientBassPositiveTransitionTrack.oldUnit, CoefficientBassPositiveTransitionTrack.newUnit,
    CoefficientBassPositiveNullTrack.laurentMovement]

variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- Pointwise evaluation in the fixed actual carrier, without a continuity assertion. -/
abbrev nativeValue (n : ℕ) (z : Carrier P p q)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :=
  CutOpenCarrier.nativeEval (polynomialReference P p q) (chartMap P (c := c))
    (laurentReference P p q) (ordinaryAnchor P p q)
    (LaurentUnitReferenceSpecialization.shiftedAnchor P p q) n z x

/-- The finite Laurent characteristic map has its complete original native family. -/
theorem laurent_parameter_native {k : ℕ}
    (N : Fin (k + 1) → Node (laurentReference P p q)) (n : ℕ)
    (z : StdSimplex ℝ (Fin (k + 1)))
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    nativeValue P p q n (includeLaurent P p q (parameter (laurentReference P p q) N z)) x =
      (mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P c))).map n
        (prespectrumFamily (laurentReference P p q) N n (z, x)) := by
  change CutOpenCarrier.nativeEval _ _ _ _ _ n
    (CutOpenCarrier.laurentInclusion _ _ _ _ _ _) x = _
  rw [CutOpenCarrier.nativeEval_laurentInclusion, pointwisePrespectrumFamily_parameter]; rfl

/-- The complete first transported family is the original family postcomposed by Laurent q. -/
theorem first_transport_family {k : ℕ}
    (N : Fin (k + 1) → Node (CoefficientLaurentUnitTenNodes.source P p)) (n : ℕ)
    (z : StdSimplex ℝ (Fin (k + 1)))
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumFamily (laurentReference P p q) (fun i ↦ firstTransport P p q (N i)) n (z, x) =
      (boundedFlatPerfectPrespectrumMap
        (coefficientMap P ((laurentUnderFunctor R).map q))).map n
          (prespectrumFamily (CoefficientLaurentUnitTenNodes.source P p) N n (z, x)) := by
  change prespectrumFamily (laurentReference P p q)
    (ModelSimplex.reanchorNodes (BassH1References.firstIso P p q)
      (fun i ↦ postcompNode (BassH1Components.laurentMap P q) (N i))) n (z, x) = _
  simp only [prespectrumFamily_reanchor, prespectrumFamily_postcomp]; rfl

/-- The complete middle transported family keeps coefficient p on the genuine native input. -/
theorem middle_transport_family {k : ℕ}
    (N : Fin (k + 1) → Node (CoefficientLaurentUnitTenNodes.source P q)) (n : ℕ)
    (z : StdSimplex ℝ (Fin (k + 1)))
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumFamily (laurentReference P p q) (fun i ↦ middleTransport P p q (N i)) n (z, x) =
      prespectrumFamily (CoefficientLaurentUnitTenNodes.source P q) N n
        (z, (boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x) := by
  change prespectrumFamily (laurentReference P p q)
    (ModelSimplex.reanchorNodes (BassH1References.middleIso P p q)
      (fun i ↦ precompNode (BassH1Components.coefficientMapModel P p) (N i))) n (z, x) = _
  simp only [prespectrumFamily_reanchor, prespectrumFamily_precomp]; rfl

/-- The actual cone map agrees with Laurent q on every inclusion point. -/
theorem cone_inclusion (n : ℕ)
    (y : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj b)))).space n) :
    (mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P c))).map n
      ((boundedFlatPerfectPrespectrumMap
        (coefficientMap P ((laurentUnderFunctor R).map q))).map n y) =
    (boundedFlatCoefficientBassPositiveConeMap P q).map n
      ((mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P b))).map n y) :=
  (congrArg (fun h ↦ h.map n y)
    (boundedFlatCoefficientBassPositiveConeMap_inclusion P q)).symm

end Quillen.PerfectComplexes.CoefficientBassPositiveLeftNativeFamilies
