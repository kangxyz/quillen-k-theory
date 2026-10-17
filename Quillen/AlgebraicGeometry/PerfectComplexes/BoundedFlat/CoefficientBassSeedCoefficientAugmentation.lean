/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedCoefficientCubeFaces
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTargetReferenceTransport
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassCutOpenAugmentationRecovery

/-! The chosen carriers and ordinary whole cone share one literal augmentation. -/
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
namespace Quillen.PerfectComplexes.CoefficientBassSeedCoefficientAugmentation
open CommonReferenceNerve CoefficientBassPositiveC1BoundaryLift
open CoefficientBassSeedTerminalAttachmentNodes
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
  (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
local notation "pa" => CategoryTheory.NatTrans.app (polynomialUnderCoefficient R) a
local notation "qa" => CategoryTheory.NatTrans.app α a
local notation "lf" => CategoryTheory.Functor.map (laurentUnderFunctor R) f
local notation "lb" => CategoryTheory.Functor.obj (laurentUnderFunctor R) b
local notation "E" => CoefficientBassSeedCarrierLaurentReference.inputReference P pa qa
local notation "D" => targetPolynomial P f α
local notation "G" => targetLaurent P f α
local notation "J" => CoefficientBassSeedTargetChartAttachment.Jb P (b := lb)

/-- The target ordinary cone has the actual postcomposed input reference. -/
abbrev input := CoefficientBassSeedTargetReferenceTransport.targetInput P lf E

/-- The original Laurent normalization is retained before entering the whole target reference. -/
def referenceIso :
    (BassProjectionPath.WholeReference.reference P lb (input P f α)).functor ≅ (G).functor :=
  CoefficientBassSeedTargetReferenceTransport.referenceIso P lf E
    (laurentReference P pa qa) (CoefficientBassSeedCarrierLaurentReference.referenceIso P pa qa)

/-- The unchanged ordinary full two-chart cone supplies the base sector. -/
abbrev base := FourEdgeTree.cone (input P f α)
  (BassH0Merge.normalizedMap (polynomialProjection P lb))
  (BassProjectionPath.WholeReference.reference P lb (input P f α))
  (BassProjectionPath.WholeReference.FourEdge.beta P lb (input P f α))

/-- The entire post-action Laurent nerve attaches through its full reference isomorphism. -/
def laurentMap : CutOpenCarrier.parameterSSet G ⟶ base P f α :=
  nerveMap (Codiscrete.functorOfFun (CommonReferenceProduct.reanchor (referenceIso P f α))) ≫
    FourEdgeTree.coneLaurent (input P f α)
      (BassH0Merge.normalizedMap (polynomialProjection P lb))
      (BassProjectionPath.WholeReference.reference P lb (input P f α))
      (BassProjectionPath.WholeReference.FourEdge.beta P lb (input P f α))

/-- Both original target-action sheets retain their exact anchors and separate tips. -/
abbrev scalar := CutOpenAugmentation.simplicial D J G
  (ordinary P f α) (shifted P f α) (base P f α) (laurentMap P f α)

/-- The realized target coefficient augmentation with both original sheets and the full cone
base. -/
abbrev space : TopCat.{u + 1} := |scalar P f α|

/-- The common chosen-Q carrier enters through its literal two original sheets. -/
def chosenMap : C(CoefficientBassSeedTerminalCarrierMap.targetCarrier P f α, space P f α) :=
  CutOpenAugmentation.continuousMap D J G (ordinary P f α) (shifted P f α)
    (base P f α) (laurentMap P f α)

/-- The ordinary cone sector enters the same augmentation without changing its cylinder clock. -/
def ordinaryMap : C(BassProjectionPath.WholeReference.FourEdge.scalarCone P lb (input P f α),
    space P f α) :=
  (SSet.toTop.map (CutOpenAugmentation.baseIn D J G (ordinary P f α) (shifted P f α)
    (base P f α) (laurentMap P f α))).hom

/-- The whole common Laurent summand has one literal attachment on both sides. -/
theorem laurent_join :
    CutOpenCarrier.left₀ D J G (ordinary P f α) ≫
      CutOpenCarrier.left₁ D J G (ordinary P f α) (shifted P f α) ≫
      CutOpenAugmentation.map D J G (ordinary P f α) (shifted P f α)
        (base P f α) (laurentMap P f α) =
    laurentMap P f α ≫ CutOpenAugmentation.baseIn D J G
      (ordinary P f α) (shifted P f α) (base P f α) (laurentMap P f α) :=
  CutOpenAugmentation.map_laurent D J G (ordinary P f α) (shifted P f α)
    (base P f α) (laurentMap P f α)

/-- The exact augmented evaluator is the existing full native Bass-cone evaluator. -/
def nativeEval (n : ℕ) : space P f α →
    (prespectrum (modelOf (boundedFlatPerfectWaldhausen
      (Scheme.BaseChange.Coefficients.space (op P, a))))).space n →
    (BassProjectionPath.WholeReference.FourEdge.nativeBassCone P lb).space n :=
  BassProjectionPath.WholeReference.FourEdge.augmentedEval P lb (input P f α) D G
    (referenceIso P f α) (ordinary P f α) (shifted P f α) n

/-- Every chosen-carrier point retains its original supported native value. -/
theorem chosenMap_native (n : ℕ)
    (z : CoefficientBassSeedTerminalCarrierMap.targetCarrier P f α)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen
      (Scheme.BaseChange.Coefficients.space (op P, a))))).space n) :
    nativeEval P f α n (chosenMap P f α z) x =
      (boundedFlatCoefficientBassPositiveConeInclusion P lb).map n
        (CutOpenCarrier.nativeEval D J G (ordinary P f α) (shifted P f α) n z x) :=
  BassProjectionPath.WholeReference.FourEdge.augmentedEval_originalMap P lb (input P f α)
    D G (referenceIso P f α) (ordinary P f α) (shifted P f α) n z x

/-- Every ordinary-cone point retains its original full native evaluator. -/
theorem ordinaryMap_native (n : ℕ)
    (z : BassProjectionPath.WholeReference.FourEdge.scalarCone P lb (input P f α)) :
    nativeEval P f α n (ordinaryMap P f α z) =
      BassProjectionPath.WholeReference.FourEdge.coneEval P lb (input P f α) n z :=
  BassProjectionPath.WholeReference.FourEdge.augmentedEval_base P lb (input P f α)
    D G (referenceIso P f α) (ordinary P f α) (shifted P f α) n z

end Quillen.PerfectComplexes.CoefficientBassSeedCoefficientAugmentation
