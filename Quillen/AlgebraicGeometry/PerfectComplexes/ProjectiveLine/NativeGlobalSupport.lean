/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeGlobalBundle
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeSupportedBijection

/-! # Original native Phi with literal inverse-image support on qcqs schemes

The global original ambient theorem discharges the localization five-lemma
premises on the base and its compact open. The supported equivalence keeps
the original forward map and original product K-equivalence in every
connective degree, including zero.
-/
@[expose] public section

open Quillen.Waldhausen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry
namespace Quillen.PerfectComplexes.ProjectiveLine
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.ProjectiveLine Waldhausen

variable (X : QuasiCompactSchemes.{u}) [QuasiSeparatedSpace X.obj] (Z : X.obj.Opens)
  [CompactSpace Z.toScheme]

/-- Original supported native Phi is bijective on the literal inverse-image open, including K0. -/
theorem nativeSupportedPreimageTwoSummandKMap_qcqs_bijective (n : ℕ) :
    Function.Bijective (nativeSupportedPreimageTwoSummandKMap X Z n) :=
  nativeSupportedPreimageTwoSummandKMap_bijective_of_ambient_degrees X Z n
    (nativeTwoSummandKMap_qcqs_bijective X (n + 1))
    (nativeTwoSummandKMap_qcqs_bijective (nativeOpenBase X Z) (n + 1))
    (nativeTwoSummandKMap_qcqs_bijective X n)
    (nativeTwoSummandKMap_qcqs_bijective (nativeOpenBase X Z) n)

/-- The supported native qcqs equivalence has exactly the original forward map. -/
def nativeGlobalSupportedPreimageTwoSummandKEquiv (n : ℕ) :
    PerfectSupportedK Z.ι n × PerfectSupportedK Z.ι n ≃*
      PerfectSupportedK ((nativeProjection.app X).hom ⁻¹ᵁ Z).ι n :=
  MulEquiv.ofBijective (nativeSupportedPreimageTwoSummandKMap X Z n)
    (nativeSupportedPreimageTwoSummandKMap_qcqs_bijective X Z n)

lemma nativeGlobalSupportedPreimageTwoSummandKEquiv_apply (n : ℕ)
    (x : PerfectSupportedK Z.ι n × PerfectSupportedK Z.ι n) :
    nativeGlobalSupportedPreimageTwoSummandKEquiv X Z n x =
      nativeSupportedPreimageTwoSummandKMap X Z n x := rfl

/-- The equivalence retains the original supported homomorphism by a literal identity. -/
lemma nativeGlobalSupportedPreimageTwoSummandKEquiv_toMonoidHom (n : ℕ) :
    (nativeGlobalSupportedPreimageTwoSummandKEquiv X Z n).toMonoidHom =
      nativeSupportedPreimageTwoSummandKMap X Z n := rfl

/-- The forward map retains the unchanged original product K-equivalence. -/
lemma nativeGlobalSupportedPreimageTwoSummandKEquiv_product (n : ℕ)
    (x : PerfectSupportedK Z.ι n × PerfectSupportedK Z.ι n) :
    nativeGlobalSupportedPreimageTwoSummandKEquiv X Z n x =
      KMap (nativeSupportedPreimageTwoSummands_exact X Z) n
        ((Product.KEquiv (perfectSupportedWaldhausen Z.ι)
          (perfectSupportedWaldhausen Z.ι) n).symm x) := rfl

end Quillen.PerfectComplexes.ProjectiveLine
