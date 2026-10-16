/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.ScalarSelfTrackBoundaryKZero
public import QuillenTest.SmallModelHomExt

/-! # The original boundary equation on arbitrary K-zero classes and literal cone objects -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Quillen.PerfectComplexes
open Quillen.Waldhausen.IteratedS
universe u
namespace QuillenTest.ScalarSelfTrackBoundaryKZero
variable {U X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
  (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

/-- The original fine boundary equation holds for an arbitrary original K-zero input. -/
theorem arbitrary_original_kzero (a : PerfectK X 0) :
    qcqsPerfectConnectingHom j 0
        (originalKSelfTrackOperation (perfectWaldhausen X) (perfectWaldhausen U)
          (perfectFlatUnitHomotopy j q) 0 a) =
      perfectAcyclicSupportedKEquiv j 0 (perfectOpenScalarConeKMap j r q hq 0 a) :=
  DFunLike.congr_fun (qcqsPerfectConnectingHom_comp_selfTrack_scalarCone j r q hq) a

/-- Object evaluation retains the literal original relative scalar cone, with no regularity. -/
theorem original_scalar_cone_object (K : Perfect X) :
    qcqsPerfectConnectingHom j 0
        (originalKSelfTrackOperation (perfectWaldhausen X) (perfectWaldhausen U)
          (perfectFlatUnitHomotopy j q) 0 ((perfectWaldhausen X).kZeroObjectClass K)) =
      perfectAcyclicSupportedKEquiv j 0
        ((Quillen.Waldhausen.Fibration.acyclicStructure (perfectOpenNested j)).kZeroObjectClass
          (perfectOpenScalarCone j r q hq K)) := by
  rw [← perfectOpenScalarConeKMap_objectClass]
  exact qcqsPerfectConnectingHom_selfTrack_scalarCone_object j r q hq K

end QuillenTest.ScalarSelfTrackBoundaryKZero
