/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.ScalarCofiberFiberComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.ScalarCofiberInputDescent
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenLongExactSequence

/-! # The original scalar self-track boundary on every connective K-group

The constructed whole canonical fiber comparison holds on every actual subdivision input.
The original forward input surjectivity and original supported-to-fiber bijectivity identify
both full boundary homomorphisms. The cone remains the same exact acyclic cone functor,
followed by the actual supported equivalence. Only the original open immersion is required.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.Fibration Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q) (n : ℕ)

/-- The normalized scalar operation has the positive supported cone boundary in all degrees. -/
theorem perfectOpenConnectingHom_comp_scalarSelfTrack :
    (perfectOpenConnectingHom j n).comp
      (originalKSelfTrackOperation (perfectWaldhausen X) (perfectOpenWeakWaldhausen j)
        (perfectOpenScalarPrespectrumHomotopy j r q hq) n) =
      (perfectAcyclicSupportedKEquiv j n).toMonoidHom.comp
        (perfectOpenScalarConeKMap j r q hq n) := by
  apply perfectScalarProjectionInputCube_hom_ext X n
  intro p
  apply (perfectSupportedFiberKMap_bijective j n).injective
  exact (perfectSupportedFiberKMap_connecting j n _).trans
    ((perfectOpenScalarKOperation_connecting_cube j r q hq n p).trans (by
      change canonicalFiberKMap (perfectOpenNested j) n _ =
        canonicalFiberKMap (perfectOpenNested j) n
          ((perfectAcyclicSupportedKEquiv j n).symm
            (perfectAcyclicSupportedKEquiv j n
              (perfectOpenScalarConeKMap j r q hq n
                (⟦perfectScalarProjectionInputCube n p⟧ : PerfectK X n))))
      rw [MulEquiv.symm_apply_apply]
      rfl))

/-- The raw original scalar track retains the same full supported boundary homomorphism. -/
theorem perfectOpenConnectingHom_comp_scalarOriginalSelfTrack :
    (perfectOpenConnectingHom j n).comp
      (originalKSelfTrackOperation (perfectWaldhausen X) (perfectOpenWeakWaldhausen j)
        (perfectOpenScalarOriginalHomotopy j r q hq) n) =
      (perfectAcyclicSupportedKEquiv j n).toMonoidHom.comp
        (perfectOpenScalarConeKMap j r q hq n) := by
  apply perfectScalarProjectionInputCube_hom_ext X n
  intro p
  apply (perfectSupportedFiberKMap_bijective j n).injective
  exact (perfectSupportedFiberKMap_connecting j n _).trans
    ((perfectOpenScalarOriginalKOperation_connecting_cube j r q hq n p).trans (by
      change canonicalFiberKMap (perfectOpenNested j) n _ =
        canonicalFiberKMap (perfectOpenNested j) n
          ((perfectAcyclicSupportedKEquiv j n).symm
            (perfectAcyclicSupportedKEquiv j n
              (perfectOpenScalarConeKMap j r q hq n
                (⟦perfectScalarProjectionInputCube n p⟧ : PerfectK X n))))
      rw [MulEquiv.symm_apply_apply]
      rfl))

/-- Every original class, including K-zero, has this normalized scalar boundary. -/
theorem perfectOpenConnectingHom_scalarSelfTrack (a : PerfectK X n) :
    perfectOpenConnectingHom j n
      (originalKSelfTrackOperation (perfectWaldhausen X) (perfectOpenWeakWaldhausen j)
        (perfectOpenScalarPrespectrumHomotopy j r q hq) n a) =
      perfectAcyclicSupportedKEquiv j n (perfectOpenScalarConeKMap j r q hq n a) :=
  DFunLike.congr_fun (perfectOpenConnectingHom_comp_scalarSelfTrack j r q hq n) a

/-- Every original class retains the raw scalar operation and the same positive cone. -/
theorem perfectOpenConnectingHom_scalarOriginalSelfTrack (a : PerfectK X n) :
    perfectOpenConnectingHom j n
      (originalKSelfTrackOperation (perfectWaldhausen X) (perfectOpenWeakWaldhausen j)
        (perfectOpenScalarOriginalHomotopy j r q hq) n a) =
      perfectAcyclicSupportedKEquiv j n (perfectOpenScalarConeKMap j r q hq n a) :=
  DFunLike.congr_fun (perfectOpenConnectingHom_comp_scalarOriginalSelfTrack j r q hq n) a

end Quillen.PerfectComplexes
