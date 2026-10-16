/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarCofiberFiberComponent
public import Quillen.Topology.HomotopyFiber.ConnectingLoopPathClass
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenLongExactSequence

/-! # Boundary of the original normalized forward scalar loop

The inverse orientation of the original scalar-cofiber loop and the negative
coordinate-transpose sign cancel. The actual original connecting homomorphism
therefore sends the forward scalar loop to its original supported cofiber class.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open Quillen.PerfectComplexes
open Quillen.Waldhausen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.Fibration
open scoped Topology
universe u
namespace Quillen.BassLaurentUnitBoundary
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (K : Perfect X)

/-- The actual normalized path is the inverse of the original component equivalence. -/
theorem scalar_normalized_component
    (α : Path ((perfectOpenNested j).coarse.kZeroObjectLoop K)
      ((perfectOpenNested j).coarse.kZeroObjectLoop K)) :
    HomotopyGroup.pi1MulEquivFundamentalGroup.symm
      (⟦perfectOpenObjectLoopNormalizedPath j K α⟧ : FundamentalGroup _ (Path.refl _)) =
    ((perfectOpenNested j).coarse.identityCofiberComponentEquiv K 1).symm
      (HomotopyGroup.pi1MulEquivFundamentalGroup.symm ⟦α⟧) := by
  apply HomotopyGroup.pi1MulEquivFundamentalGroup.injective
  rw [MulEquiv.apply_symm_apply]
  have hc := perfectOpenObjectLoopKOneNormalization_path j K α
  rw [perfectOpenObjectLoopKOneNormalization_component, MulEquiv.apply_symm_apply] at hc
  exact hc.symm

/-- Undoing the loop shift of the actual normalized path is exactly the existing K-one class. -/
theorem scalar_normalized_class
    (α : Path ((perfectOpenNested j).coarse.kZeroObjectLoop K)
      ((perfectOpenNested j).coarse.kZeroObjectLoop K)) :
    (loopShiftMulEquiv 0).symm
      (HomotopyGroup.pi1MulEquivFundamentalGroup.symm
        (⟦perfectOpenObjectLoopNormalizedPath j K α⟧ : FundamentalGroup _ (Path.refl _))) =
      perfectOpenObjectLoopKOneNormalization j K ⟦α⟧ := by
  apply (loopShiftMulEquiv 0).injective
  apply HomotopyGroup.pi1MulEquivFundamentalGroup.injective
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  exact (perfectOpenObjectLoopKOneNormalization_path j K α).symm

/-- Translating the actual normalized loop recovers the original object-component class. -/
theorem scalarComponentLoop_normalized
    (α : Path ((perfectOpenNested j).coarse.kZeroObjectLoop K)
      ((perfectOpenNested j).coarse.kZeroObjectLoop K)) :
    (⟦scalarComponentLoop j K (perfectOpenObjectLoopNormalizedPath j K α)⟧ :
      FundamentalGroup _ ((perfectOpenNested j).coarse.kZeroObjectLoop K)) = ⟦α⟧ := by
  rw [← scalarComponentLoop_class, scalar_normalized_component,
    Equiv.apply_symm_apply, MulEquiv.apply_symm_apply]

variable (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

/-- The original normalized boundary loop lies in the original cofiber's actual fiber component. -/
theorem scalar_normalized_fiber_joined :
    Joined
      (HomotopyFiber.loopInclusion
        (basedLoopMap (changeWeakMap (perfectOpenNested j)) (changeWeakMap_basepoint _))
        (Path.refl (perfectOpenNested j).coarse.kBasepoint)
        (Path.refl (perfectWaldhausen X).kBasepoint) (basedLoopMap_refl _ _)
        (perfectOpenObjectLoopNormalizedPath j K (perfectScalarCofiberBoundaryLoop j r q hq K)))
      (canonicalFiberObjectLoopTranspose (perfectOpenNested j)
        (perfectOpenScalarCofiberAcyclic j r q hq K)) := by
  let β := perfectScalarCofiberBoundaryLoop j r q hq K
  let β₀ := perfectOpenObjectLoopNormalizedPath j K β
  let e := scalarFiberComponentEquiv j K
  apply joined_of_equiv e
  have p₁ := componentLoopFiberPath (changeWeakMap (perfectOpenNested j))
    (changeWeakMap_basepoint (perfectOpenNested j)) ((perfectWaldhausen X).kZeroObjectLoop K)
    ((perfectOpenNested j).coarse.kZeroObjectLoop K)
    (deloopingMap_kZeroObjectLoop (changeWeak_exact (perfectOpenNested j))
      (perfectOpenNested j).zero_eq.symm K)
    ((perfectWaldhausen X).identityCofiberSuffixPath K) β₀
  obtain ⟨H⟩ := Quotient.exact (scalarComponentLoop_normalized j K β)
  let p₂ := (pathOfPathHomotopy H).map
    (HomotopyFiber.loopInclusion
      (basedLoopMap (changeWeakMap (perfectOpenNested j)) (changeWeakMap_basepoint _))
      ((perfectOpenNested j).coarse.kZeroObjectLoop K)
      ((perfectWaldhausen X).kZeroObjectLoop K)
      (deloopingMap_kZeroObjectLoop (changeWeak_exact (perfectOpenNested j))
        (perfectOpenNested j).zero_eq.symm K)).continuous
  let p₃ := perfectScalarCofiberFiberBoundaryPath j r q hq K
  exact ⟨(p₁.symm.trans (p₂.trans p₃)).cast rfl
    (scalarFiberComponentEquiv_canonical j K _)⟩

/-- The original fiber-loop homeomorphism retains the normalized cofiber loop class. -/
theorem scalar_normalized_fiber_loop_class :
    (⟦HomotopyFiber.loopConnectingMap (changeWeakMap (perfectOpenNested j))
      (changeWeakMap_basepoint _)
      (perfectOpenObjectLoopNormalizedPath j K (perfectScalarCofiberBoundaryLoop j r q hq K))⟧ :
      FundamentalGroup _ (HomotopyFiber.basepoint _ _ _ (changeWeakMap_basepoint _))) =
    ⟦canonicalFiberObjectLoop (perfectOpenNested j)
      (perfectOpenScalarCofiberAcyclic j r q hq K)⟧ := by
  obtain ⟨p⟩ := scalar_normalized_fiber_joined j K r q hq
  let e := HomotopyFiber.loopFiberHomeomorph (changeWeakMap (perfectOpenNested j))
    (changeWeakMap_basepoint _)
  let p' := p.map e.continuous
  apply Quotient.sound
  exact ⟨pathHomotopyOfPath (p'.cast rfl (e.apply_symm_apply _).symm)⟩

/-- The original canonical-fiber K-map sends the original object class to its actual fiber loop. -/
theorem canonicalFiberKMap_object (A : AcyclicCategory (perfectOpenNested j)) :
    canonicalFiberKMap (perfectOpenNested j) 0
      ((acyclicStructure (perfectOpenNested j)).kZeroObjectClass A) =
    HomotopyGroup.pi1MulEquivFundamentalGroup.symm
      (⟦canonicalFiberObjectLoop (perfectOpenNested j) A⟧ : FundamentalGroup _
        (HomotopyFiber.basepoint _ _ _ (changeWeakMap_basepoint _))) := by
  apply HomotopyGroup.pi1MulEquivFundamentalGroup.injective
  change HomotopyGroup.pi1MulEquivFundamentalGroup
    (piMap 0 (canonicalFiberMap (perfectOpenNested j)) (canonicalFiberMap_basepoint _)
      (HomotopyGroup.pi1MulEquivFundamentalGroup.symm
        ⟦(acyclicStructure (perfectOpenNested j)).kZeroObjectLoop A⟧)) = _
  rw [piOneEquivFundamentalGroup_naturality, MulEquiv.apply_symm_apply,
    MulEquiv.apply_symm_apply, FundamentalGroup.mapOfEq_apply]
  rfl

/-- The actual topological connecting map of the original forward scalar loop is its cofiber. -/
theorem scalar_forward_fiber_boundary :
    HomotopyFiber.connectingHom (changeWeakMap (perfectOpenNested j))
      (perfectOpenNested j).coarse.kBasepoint (perfectWaldhausen X).kBasepoint
      (changeWeakMap_basepoint _) 0 (perfectScalarForwardKOneClass j K r q hq) =
    canonicalFiberKMap (perfectOpenNested j) 0
      ((acyclicStructure (perfectOpenNested j)).kZeroObjectClass
        (perfectOpenScalarCofiberAcyclic j r q hq K)) := by
  have hs := connectingHom_loop_path (changeWeakMap (perfectOpenNested j))
    (changeWeakMap_basepoint _)
    (perfectOpenObjectLoopNormalizedPath j K (perfectScalarCofiberBoundaryLoop j r q hq K))
  rw [scalar_normalized_class] at hs
  change _ = HomotopyFiber.connectingHom _ _ _ _ 0
    (perfectScalarCofiberBoundaryKOneClass j K r q hq)⁻¹ at hs
  rw [perfectScalarCofiberBoundaryKOneClass_eq_inv, inv_inv] at hs
  rw [← hs, canonicalFiberKMap_object, scalar_normalized_fiber_loop_class]

/-- No boundary compatibility is assumed: the original relative boundary is the cofiber class. -/
theorem scalar_forward_changeWeak_boundary :
    changeWeakConnectingHom (perfectOpenNested j)
      (perfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence j) 0
      (perfectScalarForwardKOneClass j K r q hq) =
    (acyclicStructure (perfectOpenNested j)).kZeroObjectClass
      (perfectOpenScalarCofiberAcyclic j r q hq K) := by
  apply (canonicalFiberKMap_bijective_of_weak (perfectOpenNested j)
    (perfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence j) 0).injective
  rw [canonicalFiberKMap_connecting, scalar_forward_fiber_boundary]

end Quillen.BassLaurentUnitBoundary
