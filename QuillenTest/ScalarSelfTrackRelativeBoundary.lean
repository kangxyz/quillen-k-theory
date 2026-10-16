/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.ScalarSelfTrackRelativeBoundary

/-! Strict all-degree consumers of the original relative scalar boundary, without compactness. -/
@[expose] public section
noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
open CategoryTheory AlgebraicGeometry
open Quillen Quillen.PerfectComplexes Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u
namespace QuillenTest.ScalarSelfTrackRelativeBoundary
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

/-- The complete normalized original homomorphism has the same actual cone map. -/
theorem original_normalized_hom (n : ℕ) :
    (perfectOpenConnectingHom j n).comp
      (originalKSelfTrackOperation (perfectWaldhausen X) (perfectOpenWeakWaldhausen j)
        (perfectOpenScalarPrespectrumHomotopy j r q hq) n) =
      (perfectAcyclicSupportedKEquiv j n).toMonoidHom.comp
        (perfectOpenScalarConeKMap j r q hq n) :=
  perfectOpenConnectingHom_comp_scalarSelfTrack j r q hq n

/-- An arbitrary original input retains the raw scalar track and full supported endpoint. -/
theorem original_raw_class (n : ℕ) (a : PerfectK X n) :
    perfectOpenConnectingHom j n
      (originalKSelfTrackOperation (perfectWaldhausen X) (perfectOpenWeakWaldhausen j)
        (perfectOpenScalarOriginalHomotopy j r q hq) n a) =
      perfectAcyclicSupportedKEquiv j n (perfectOpenScalarConeKMap j r q hq n a) :=
  perfectOpenConnectingHom_scalarOriginalSelfTrack j r q hq n a

/-- The normalized K-zero result holds on every original class without object generators. -/
theorem original_normalized_kzero (a : PerfectK X 0) :
    perfectOpenConnectingHom j 0
      (originalKSelfTrackOperation (perfectWaldhausen X) (perfectOpenWeakWaldhausen j)
        (perfectOpenScalarPrespectrumHomotopy j r q hq) 0 a) =
      perfectAcyclicSupportedKEquiv j 0 (perfectOpenScalarConeKMap j r q hq 0 a) :=
  perfectOpenConnectingHom_scalarSelfTrack j r q hq 0 a

/-- The raw K-zero result keeps the actual original scalar operation. -/
theorem original_raw_kzero (a : PerfectK X 0) :
    perfectOpenConnectingHom j 0
      (originalKSelfTrackOperation (perfectWaldhausen X) (perfectOpenWeakWaldhausen j)
        (perfectOpenScalarOriginalHomotopy j r q hq) 0 a) =
      perfectAcyclicSupportedKEquiv j 0 (perfectOpenScalarConeKMap j r q hq 0 a) :=
  perfectOpenConnectingHom_scalarOriginalSelfTrack j r q hq 0 a

end QuillenTest.ScalarSelfTrackRelativeBoundary
