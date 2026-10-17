/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTerminalAttachmentNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCutOpenPrecompNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveC0CarrierSeed

/-! Genuine input precomposition and both terminal attachments of the original target carrier. -/
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
namespace Quillen.PerfectComplexes.CoefficientBassSeedTerminalCarrierMap
open CommonReferenceNerve
open CoefficientBassPositiveC1BoundaryLift CoefficientBassSeedTerminalAttachmentNodes
open LaurentUnitReferenceSpecialization (commonUnit)
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
  (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
local notation "pb" => CategoryTheory.NatTrans.app (polynomialUnderCoefficient R) b
local notation "qb" => CategoryTheory.NatTrans.app α b
local notation "U" => BassMWholeNerve.coefficientModel P f
local notation "K" => CoefficientBassSeedTargetChartAttachment.Jb P
  (b := CategoryTheory.Functor.obj (laurentUnderFunctor R) b)

/-- The common post-action reference carrier retains two distinct original sheet tips. -/
abbrev targetCarrier := CutOpenCarrier.space
  (targetPolynomial P f α) K (targetLaurent P f α) (ordinary P f α) (shifted P f α)

/-- First precompose the genuine input, then apply both proved terminal attachment squares. -/
def carrierMap : C(CoefficientBassPositiveC0CarrierSeed.Carrier P pb qb, targetCarrier P f α) :=
  (CoefficientBassSeedTerminalAttachmentMap.map P f α).hom.comp
    (CutOpenPrecomp.map U (polynomialReference P pb qb) K (laurentReference P pb qb)
      (ordinaryAnchor P pb qb) (commonUnit P pb qb ≪≫ ordinaryAnchor P pb qb)).hom

/-- Every native input is the actual coefficient image, with no identity cancellation. -/
theorem carrierMap_native (n : ℕ) (y : CoefficientBassPositiveC0CarrierSeed.Carrier P pb qb)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen
      (Scheme.BaseChange.Coefficients.space (op P, a))))).space n) :
    CutOpenCarrier.nativeEval (targetPolynomial P f α) K (targetLaurent P f α)
      (ordinary P f α) (shifted P f α) n (carrierMap P f α y) x =
    CutOpenCarrier.nativeEval (polynomialReference P pb qb) K (laurentReference P pb qb)
      (ordinaryAnchor P pb qb) (commonUnit P pb qb ≪≫ ordinaryAnchor P pb qb) n y
      ((prespectrumMap U).map n x) := by
  dsimp only [carrierMap, ContinuousMap.comp_apply]
  rw [CoefficientBassSeedTerminalAttachmentNative.map_native]
  exact CutOpenPrecomp.map_native U (polynomialReference P pb qb) K
    (laurentReference P pb qb) (ordinaryAnchor P pb qb)
    (commonUnit P pb qb ≪≫ ordinaryAnchor P pb qb) n y x

end Quillen.PerfectComplexes.CoefficientBassSeedTerminalCarrierMap
