/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarConeFunctor

/-! # The original supported and relative-acyclic scalar cone K-maps

The literal relative-acyclic cone functor is the original supported cone functor followed by
its existing support-equivalence inverse. Composition of the original K-maps and cancellation
of that actual equivalence identify both presentations in every connective degree.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen
universe u
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q) (n : ℕ)

/-- The actual acyclic cone map retains the literal inverse support-equivalence factor. -/
theorem perfectOpenScalarConeKMap_eq_supported :
    perfectOpenScalarConeKMap j r q hq n =
      (perfectAcyclicSupportedKEquiv j n).symm.toMonoidHom.comp
        (perfectSupportedScalarConeKMap j r q hq n) := by
  change KMap ((perfectSupportedScalarConeFunctor_waldhausenExact j r q hq).comp
    (perfectSupportedToAcyclic_exact j)) n =
      (KMap (perfectSupportedToAcyclic_exact j) n).comp
        (KMap (perfectSupportedScalarConeFunctor_waldhausenExact j r q hq) n)
  exact (KMap_comp_KMap (perfectSupportedScalarConeFunctor_waldhausenExact j r q hq)
    (perfectSupportedToAcyclic_exact j) n).symm

/-- The original equivalence cancels without replacing either cone K-map. -/
theorem perfectAcyclicSupportedKEquiv_comp_scalarConeKMap :
    (perfectAcyclicSupportedKEquiv j n).toMonoidHom.comp
        (perfectOpenScalarConeKMap j r q hq n) =
      perfectSupportedScalarConeKMap j r q hq n := by
  apply MonoidHom.ext
  intro a
  have h := DFunLike.congr_fun (perfectOpenScalarConeKMap_eq_supported j r q hq n) a
  change perfectAcyclicSupportedKEquiv j n (perfectOpenScalarConeKMap j r q hq n a) = _
  rw [h]
  exact (perfectAcyclicSupportedKEquiv j n).apply_symm_apply _

/-- Every original class gives the same supported cone, including degree zero. -/
theorem perfectAcyclicSupportedKEquiv_scalarConeKMap (a : PerfectK X n) :
    perfectAcyclicSupportedKEquiv j n (perfectOpenScalarConeKMap j r q hq n a) =
      perfectSupportedScalarConeKMap j r q hq n a :=
  DFunLike.congr_fun (perfectAcyclicSupportedKEquiv_comp_scalarConeKMap j r q hq n) a

end Quillen.PerfectComplexes
