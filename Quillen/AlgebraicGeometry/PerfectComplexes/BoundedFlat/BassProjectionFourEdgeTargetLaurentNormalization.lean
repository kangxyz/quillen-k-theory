/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeTargetConeReference

/-! The ordinary Laurent action is the existing full target-reference transport. -/
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
namespace Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.TargetCone
open BassH0Merge CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
open CoefficientBassSeedTargetH0Reference CoefficientBassSeedTargetReferenceTransport
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
variable {V : Model.{u + 1}}
  (E : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
  (G : V ⟶ modelOf (boundedFlatPerfectWaldhausen
    (space (op P, (laurentUnderFunctor R).obj a))))
  (τ : (WholeReference.reference P a E).functor ≅ G.functor)
local notation "L" => Target.sourcePost P f

/-- The original H0 source and target anchors give the exact existing Laurent reference word. -/
theorem source_action_anchor :
    ((Target.terminalBoundaryAnchor P f E).symm ≪≫ Target.sourceBoundaryAnchor P f E) ≪≫
        isoWhiskerRight τ (L).functor =
      CoefficientBassSeedTargetReferenceTransport.referenceIso P f E G τ := by
  have ht : targetReferenceIso P f E G τ = (Target.terminalBoundaryAnchor P f E).symm := by
    exact (Iso.symm_symm_eq _).symm.trans
      (congrArg Iso.symm (Target.targetReferenceIso_symm P f E G τ))
  have h := reference_triangle P f E G τ
  rw [ht] at h
  simpa only [referenceBridge, Target.sourceBoundaryAnchor, Iso.trans_assoc] using h

/-- The entire dependent node retains the actual old reference before coefficient action. -/
theorem sourceNode_reanchor (N : CommonReferenceNerve.Node G) :
    sourceNode P f E (CommonReferenceProduct.reanchor τ N) =
      CoefficientBassSeedTargetReferenceTransport.nodeMap P f E G τ N := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  change (Target.terminalBoundaryAnchor P f E).symm ≪≫
      (Target.sourceBoundaryAnchor P f E ≪≫ isoWhiskerRight (τ ≪≫ N.2) (L).functor) =
    CoefficientBassSeedTargetReferenceTransport.referenceIso P f E G τ ≪≫
      isoWhiskerRight N.2 (L).functor
  rw [isoWhiskerRight_trans]
  calc
    _ = (((Target.terminalBoundaryAnchor P f E).symm ≪≫
        Target.sourceBoundaryAnchor P f E) ≪≫ isoWhiskerRight τ (L).functor) ≪≫
      isoWhiskerRight N.2 (L).functor := by simp only [Iso.trans_assoc]
    _ = _ := congrArg (fun e ↦ e ≪≫ isoWhiskerRight N.2 (L).functor)
      (source_action_anchor P f E G τ)

/-- The full Laurent realization follows the same original target-reference map. -/
theorem laurent_reanchor (y : |parameterSSet G|) :
    laurent P f E (mapParameter (CommonReferenceProduct.reanchor τ) y) =
      CoefficientBassSeedTargetReferenceTransport.parameterMap P f E G τ y := by
  obtain ⟨k, N, z, rfl⟩ := exists_parameter G y
  change mapParameter (sourceNode P f E)
      (mapParameter (CommonReferenceProduct.reanchor τ) (CommonReferenceNerve.parameter G N z)) =
    mapParameter (CoefficientBassSeedTargetReferenceTransport.nodeMap P f E G τ)
      (CommonReferenceNerve.parameter G N z)
  rw [mapParameter_parameter, mapParameter_parameter, mapParameter_parameter]
  apply congrArg (fun ns ↦ CommonReferenceNerve.parameter
    (WholeReference.reference P b (E ≫ normalizedMap (coefficientMap P f))) ns z)
  funext i
  exact sourceNode_reanchor P f E G τ (N i)

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.TargetCone
