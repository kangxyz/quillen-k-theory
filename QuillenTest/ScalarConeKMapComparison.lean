/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.ScalarConeKMapComparison

/-! # Clients of the original scalar-cone support comparison -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes
universe u
namespace QuillenTest.ScalarConeKMapComparison
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

/-- The entire map into acyclic objects uses the existing supported-equivalence inverse. -/
theorem original_inverse_factor (n : ℕ) :
    perfectOpenScalarConeKMap j r q hq n =
      (perfectAcyclicSupportedKEquiv j n).symm.toMonoidHom.comp
        (perfectSupportedScalarConeKMap j r q hq n) :=
  perfectOpenScalarConeKMap_eq_supported j r q hq n

/-- The original equivalence cancels on the complete homomorphism in every degree. -/
theorem original_homomorphism (n : ℕ) :
    (perfectAcyclicSupportedKEquiv j n).toMonoidHom.comp
        (perfectOpenScalarConeKMap j r q hq n) =
      perfectSupportedScalarConeKMap j r q hq n :=
  perfectAcyclicSupportedKEquiv_comp_scalarConeKMap j r q hq n

/-- Degree zero keeps an arbitrary original class rather than an object generator. -/
theorem arbitrary_original_kzero (a : PerfectK X 0) :
    perfectAcyclicSupportedKEquiv j 0 (perfectOpenScalarConeKMap j r q hq 0 a) =
      perfectSupportedScalarConeKMap j r q hq 0 a :=
  perfectAcyclicSupportedKEquiv_scalarConeKMap j r q hq 0 a

end QuillenTest.ScalarConeKMapComparison
