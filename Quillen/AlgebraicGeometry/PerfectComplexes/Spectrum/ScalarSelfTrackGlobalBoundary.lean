/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.ScalarSelfTrackRelativeBoundary
public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.ScalarUnitTrackOperation
public import Quillen.AlgebraicGeometry.PerfectComplexes.GlobalLocalization

/-! # The original qcqs boundary of the flat-unit operation in every connective degree

The whole original scalar restriction comparison and the original relative-boundary transport
identify the actual flat-unit operation with the positive supported scalar cone map. The compact
open and qcqs hypotheses are exactly those of the existing fine localization endpoint.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TopologicalSpace
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
  (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q) (n : ℕ)

/-- The original fine unit operation has the actual supported cone boundary on every K-group. -/
theorem qcqsPerfectConnectingHom_comp_scalarUnitSelfTrack :
    (qcqsPerfectConnectingHom j n).comp
      (originalKSelfTrackOperation (perfectWaldhausen X) (perfectWaldhausen U)
        (perfectFlatUnitHomotopy j q) n) =
      (perfectAcyclicSupportedKEquiv j n).toMonoidHom.comp
        (perfectOpenScalarConeKMap j r q hq n) := by
  have hr : (perfectOpenKRestrict j (n + 1)).comp
      (originalKSelfTrackOperation (perfectWaldhausen X) (perfectOpenWeakWaldhausen j)
        (perfectOpenScalarPrespectrumHomotopy j r q hq) n) =
      originalKSelfTrackOperation (perfectWaldhausen X) (perfectWaldhausen U)
        (perfectFlatUnitHomotopy j q) n :=
    perfectOpenScalarKOperation_restrict j r q hq n
  calc
    _ = (qcqsPerfectConnectingHom j n).comp
        ((perfectOpenKRestrict j (n + 1)).comp
          (originalKSelfTrackOperation (perfectWaldhausen X) (perfectOpenWeakWaldhausen j)
            (perfectOpenScalarPrespectrumHomotopy j r q hq) n)) :=
      congrArg (fun f ↦ (qcqsPerfectConnectingHom j n).comp f) hr.symm
    _ = (perfectOpenConnectingHom j n).comp
        (originalKSelfTrackOperation (perfectWaldhausen X) (perfectOpenWeakWaldhausen j)
          (perfectOpenScalarPrespectrumHomotopy j r q hq) n) := by
      rw [← MonoidHom.comp_assoc, qcqsPerfectConnectingHom_comp_relative]
    _ = _ := perfectOpenConnectingHom_comp_scalarSelfTrack j r q hq n

/-- Every original input class retains the actual flat-pullback unit and the positive cone sign. -/
theorem qcqsPerfectConnectingHom_scalarUnitSelfTrack (a : PerfectK X n) :
    qcqsPerfectConnectingHom j n
      (originalKSelfTrackOperation (perfectWaldhausen X) (perfectWaldhausen U)
        (perfectFlatUnitHomotopy j q) n a) =
      perfectAcyclicSupportedKEquiv j n (perfectOpenScalarConeKMap j r q hq n a) :=
  DFunLike.congr_fun (qcqsPerfectConnectingHom_comp_scalarUnitSelfTrack j r q hq n) a

end Quillen.PerfectComplexes
