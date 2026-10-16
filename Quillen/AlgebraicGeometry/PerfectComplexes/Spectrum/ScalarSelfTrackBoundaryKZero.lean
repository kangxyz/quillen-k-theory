/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.ScalarRestrictionSelfTrackKZero
public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarSupportedBoundary
public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarConeFunctor
public import Quillen.Waldhausen.GrothendieckComparison.SmallModelHomExt

/-! # The actual scalar self-track boundary on all original K-zero classes

The existing object boundary retains its actual relative cofiber transport and
literal scalar cone. The original small-model equivalence then extends equality
of the two genuine homomorphisms from object loops to every original K-zero
class. The fine endpoint retains the explicit qcqs and compact-open hypotheses.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TopologicalSpace
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
  (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

/-- On each original object, the actual boundary is the same literal scalar-cone K-map. -/
theorem qcqsPerfectConnectingHom_selfTrack_scalarCone_object (K : Perfect X) :
    qcqsPerfectConnectingHom j 0
        (originalKSelfTrackOperation (perfectWaldhausen X) (perfectWaldhausen U)
          (perfectFlatUnitHomotopy j q) 0 ((perfectWaldhausen X).kZeroObjectClass K)) =
      perfectAcyclicSupportedKEquiv j 0
        (perfectOpenScalarConeKMap j r q hq 0 ((perfectWaldhausen X).kZeroObjectClass K)) := by
  have hc : perfectAcyclicSupportedKEquiv j 0
      (perfectOpenScalarConeKMap j r q hq 0 ((perfectWaldhausen X).kZeroObjectClass K)) =
      (perfectSupportedWaldhausen j).kZeroObjectClass
        ((perfectAcyclicToSupported j).obj (perfectOpenScalarCone j r q hq K)) := by
    rw [perfectOpenScalarConeKMap_objectClass]
    exact KMap_kZeroObjectClass (perfectAcyclicToSupported_exact j)
      (perfectOpenScalarCone j r q hq K)
  calc
    qcqsPerfectConnectingHom j 0
        (originalKSelfTrackOperation (perfectWaldhausen X) (perfectWaldhausen U)
          (perfectFlatUnitHomotopy j q) 0 ((perfectWaldhausen X).kZeroObjectClass K)) =
        qcqsPerfectConnectingHom j 0
          (perfectOpenKRestrict j 1 (perfectScalarForwardKOneClass j K r q hq)) :=
      congrArg (qcqsPerfectConnectingHom j 0)
        (perfectScalarForwardKOneClass_restrict_selfTrack j K r q hq).symm
    _ = perfectOpenConnectingHom j 0 (perfectScalarForwardKOneClass j K r q hq) :=
      DFunLike.congr_fun (qcqsPerfectConnectingHom_comp_relative j 0)
        (perfectScalarForwardKOneClass j K r q hq)
    _ = (perfectSupportedWaldhausen j).kZeroObjectClass
        ((perfectAcyclicToSupported j).obj (perfectOpenScalarCone j r q hq K)) :=
      perfectOpenConnectingHom_scalarForward j K r q hq
    _ = perfectAcyclicSupportedKEquiv j 0
        (perfectOpenScalarConeKMap j r q hq 0 ((perfectWaldhausen X).kZeroObjectClass K)) :=
      hc.symm

/-- The original fine boundary composite equals the actual cone map on every K-zero class. -/
theorem qcqsPerfectConnectingHom_comp_selfTrack_scalarCone :
    (qcqsPerfectConnectingHom j 0).comp
      (originalKSelfTrackOperation (perfectWaldhausen X) (perfectWaldhausen U)
        (perfectFlatUnitHomotopy j q) 0) =
      (perfectAcyclicSupportedKEquiv j 0).toMonoidHom.comp
        (perfectOpenScalarConeKMap j r q hq 0) := by
  apply AlgebraicGrothendieck.kZero_hom_ext_ofSmallModel (perfectWaldhausen X)
  intro K
  exact qcqsPerfectConnectingHom_selfTrack_scalarCone_object j r q hq K

end Quillen.PerfectComplexes
