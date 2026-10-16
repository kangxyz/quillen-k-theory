/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarForwardRelativeBoundary
public import Quillen.AlgebraicGeometry.PerfectComplexes.GlobalLocalization
public import Quillen.AlgebraicGeometry.PerfectComplexes.GlobalUnitKOneInversion

/-!
# The original fine scalar-unit boundary in supported K-zero

The existing relative scalar boundary transports through the actual acyclic-to-supported
functor and the original fine endpoint restriction. Its value is the literal supported scalar
cone object class. The fine endpoint statement requires a compact open in a qcqs scheme;
the relative statement only requires an open immersion. The rank-one statement uses the
original structure-sheaf restriction isomorphism. No excision or terminal Bass sign is asserted.
-/

@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Quillen.Waldhausen Quillen.Waldhausen.Fibration
universe u
namespace Quillen.PerfectComplexes

/-- The original relative supported boundary is the actual scalar mapping-cone object class. -/
theorem perfectOpenConnectingHom_scalarForward {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (K : Perfect X)
    (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q) :
    perfectOpenConnectingHom j 0 (perfectScalarForwardKOneClass j K r q hq) =
      (perfectSupportedWaldhausen j).kZeroObjectClass
        ((perfectAcyclicToSupported j).obj (perfectOpenScalarCone j r q hq K)) := by
  change (perfectAcyclicSupportedKEquiv j 0)
    (changeWeakConnectingHom (perfectOpenNested j)
      (perfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence j) 0
      (perfectScalarForwardKOneClass j K r q hq)) = _
  rw [Quillen.BassLaurentUnitBoundary.scalar_forward_changeWeak_boundary,
    perfectOpenScalarCofiberAcyclic_class]
  exact KMap_kZeroObjectClass (perfectAcyclicToSupported_exact j)
    (perfectOpenScalarCone j r q hq K)

variable {U X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
  (j : U ⟶ X) [IsOpenImmersion j]

/-- The fine unit class has the original supported scalar cone as its actual boundary. -/
theorem qcqsPerfectConnectingHom_globalUnit (K : Perfect X)
    (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q) :
    qcqsPerfectConnectingHom j 0
        (perfectGlobalUnitKOneClass U q ((perfectRestrict j).obj K)) =
      (perfectSupportedWaldhausen j).kZeroObjectClass
        ((perfectAcyclicToSupported j).obj (perfectOpenScalarCone j r q hq K)) := by
  rw [← perfectScalarForwardKOneClass_restrict j K r q hq]
  exact (DFunLike.congr_fun (qcqsPerfectConnectingHom_comp_relative j 0)
    (perfectScalarForwardKOneClass j K r q hq)).trans
      (perfectOpenConnectingHom_scalarForward j K r q hq)

/-- Rank one retains the actual original structure sheaf and its restriction comparison. -/
theorem qcqsPerfectConnectingHom_globalUnit_rankOne
    (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q) :
    qcqsPerfectConnectingHom j 0 (perfectGlobalUnitKOneClass U q (rankOnePerfect U)) =
      (perfectSupportedWaldhausen j).kZeroObjectClass
        ((perfectAcyclicToSupported j).obj
          (perfectOpenScalarCone j r q hq (rankOnePerfect X))) := by
  rw [← perfectGlobalUnitKOneClass_iso U q (rankOnePerfectRestrictIso j)]
  exact qcqsPerfectConnectingHom_globalUnit j (rankOnePerfect X) r q hq

/-- If the scalar restricts to the inverse unit, the original forward unit boundary is inverse
of the actual supported cone class, at the unchanged fine endpoint and object. -/
theorem qcqsPerfectConnectingHom_globalUnit_inverse_scalar (K : Perfect X)
    (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑(q⁻¹)) :
    qcqsPerfectConnectingHom j 0
        (perfectGlobalUnitKOneClass U q ((perfectRestrict j).obj K)) =
      ((perfectSupportedWaldhausen j).kZeroObjectClass
        ((perfectAcyclicToSupported j).obj (perfectOpenScalarCone j r q⁻¹ hq K)))⁻¹ := by
  have h := qcqsPerfectConnectingHom_globalUnit j K r q⁻¹ hq
  rw [perfectGlobalUnitKOneClass_inv, map_inv] at h
  simpa only [inv_inv] using congrArg Inv.inv h

end Quillen.PerfectComplexes
