/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTerminalAttachmentMap
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCutOpenEvaluation

/-! Native recovery for the actual terminal reference transport on the whole two-tip carrier. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedTerminalAttachmentNative
open CommonReferenceNerve CommonReferenceProduct CutOpenCarrier
open CoefficientBassSeedTerminalAttachmentNodes
open CoefficientBassSeedTerminalAttachmentTriangle CoefficientBassSeedTerminalShiftedTriangle
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
  (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
local notation "K" => CoefficientBassSeedTargetChartAttachment.Jb P
  (b := CategoryTheory.Functor.obj (laurentUnderFunctor R) b)
local notation "F" => sourcePolynomial P f α
local notation "G" => sourceLaurent P f α
local notation "F'" => targetPolynomial P f α
local notation "G'" => targetLaurent P f α
local notation "ε₀" => targetOrdinary P f α
local notation "ε₁" => targetShifted P f α
local notation "η₀" => ordinary P f α
local notation "η₁" => shifted P f α

open CoefficientBassSeedTerminalAttachmentMap

/-- Polynomial reanchoring preserves every original native value. -/
theorem polynomial_native (n : ℕ) (y : |parameterSSet F|)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen
      (Scheme.BaseChange.Coefficients.space (op P, a))))).space n) :
    pointwisePrespectrumFamily F' n (polynomialMap P f α y) x =
      pointwisePrespectrumFamily F n y x :=
  pointwise_reanchor (CoefficientBassSeedTerminalPolynomialReference.referenceIso P f α) n y x

/-- Laurent reanchoring preserves every original native value. -/
theorem laurent_native (n : ℕ) (y : |parameterSSet G|)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen
      (Scheme.BaseChange.Coefficients.space (op P, a))))).space n) :
    pointwisePrespectrumFamily G' n (laurentMap P f α y) x =
      pointwisePrespectrumFamily G n y x :=
  pointwise_reanchor (CoefficientBassSeedTerminalLaurentReference.referenceIso P f α) n y x

/-- The whole original chosen target carrier keeps its native value in every level. -/
theorem map_native (n : ℕ) (y : CutOpenCarrier.space F K G ε₀ ε₁)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen
      (Scheme.BaseChange.Coefficients.space (op P, a))))).space n) :
    nativeEval F' K G' η₀ η₁ n (map P f α y) x = nativeEval F K G ε₀ ε₁ n y x := by
  rcases exists_native_cell F K G ε₀ ε₁ y with
    ⟨z, rfl⟩ | ⟨z, t, rfl⟩ | ⟨z, t, rfl⟩ | rfl | rfl
  · rw [map_laurent, nativeEval_laurentInclusion, nativeEval_laurentInclusion, laurent_native]
  · rw [map_cylinderMinus, nativeEval_cylinderMinus, nativeEval_cylinderMinus, polynomial_native]
  · rw [map_cylinderPlus, nativeEval_cylinderPlus, nativeEval_cylinderPlus, polynomial_native]
  · rw [map_tipMinus, nativeEval_tipMinus, nativeEval_tipMinus]
  · rw [map_tipPlus, nativeEval_tipPlus, nativeEval_tipPlus]

end Quillen.PerfectComplexes.CoefficientBassSeedTerminalAttachmentNative
