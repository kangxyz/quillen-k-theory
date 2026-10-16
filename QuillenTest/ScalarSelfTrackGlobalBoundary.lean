/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.ScalarSelfTrackGlobalBoundary
public import QuillenTest.ScalarSelfTrackRelativeBoundary

/-! Strict consumers of the original qcqs unit boundary in every connective degree. -/
@[expose] public section
noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
open CategoryTheory AlgebraicGeometry TopologicalSpace
open Quillen Quillen.PerfectComplexes Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u
namespace QuillenTest.ScalarSelfTrackGlobalBoundary
variable {U X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
  (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

/-- The original fine boundary equality is an equality of complete homomorphisms. -/
theorem original_global_hom (n : ℕ) :
    (qcqsPerfectConnectingHom j n).comp
      (originalKSelfTrackOperation (perfectWaldhausen X) (perfectWaldhausen U)
        (perfectFlatUnitHomotopy j q) n) =
      (perfectAcyclicSupportedKEquiv j n).toMonoidHom.comp
        (perfectOpenScalarConeKMap j r q hq n) :=
  qcqsPerfectConnectingHom_comp_scalarUnitSelfTrack j r q hq n

/-- An arbitrary original input retains the actual flat-unit operation and cone. -/
theorem original_global_class (n : ℕ) (a : PerfectK X n) :
    qcqsPerfectConnectingHom j n
      (originalKSelfTrackOperation (perfectWaldhausen X) (perfectWaldhausen U)
        (perfectFlatUnitHomotopy j q) n a) =
      perfectAcyclicSupportedKEquiv j n (perfectOpenScalarConeKMap j r q hq n a) :=
  qcqsPerfectConnectingHom_scalarUnitSelfTrack j r q hq n a

/-- K-zero retains exactly the same original qcqs and compact-open hypotheses. -/
theorem original_global_kzero (a : PerfectK X 0) :
    qcqsPerfectConnectingHom j 0
      (originalKSelfTrackOperation (perfectWaldhausen X) (perfectWaldhausen U)
        (perfectFlatUnitHomotopy j q) 0 a) =
      perfectAcyclicSupportedKEquiv j 0 (perfectOpenScalarConeKMap j r q hq 0 a) :=
  qcqsPerfectConnectingHom_scalarUnitSelfTrack j r q hq 0 a

end QuillenTest.ScalarSelfTrackGlobalBoundary
