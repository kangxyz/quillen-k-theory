/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.Coherent.Affine.PrincipalSupport
public import Quillen.GTheory.SmallModelLocalization

/-!
# Genuine G-theory localization for a principal open of a noetherian affine scheme

Let `R` be a commutative noetherian ring and let `r : R`. The theorem here
uses actual coherent sheaves on `Spec R`, actual geometric restriction to
`Spec R[1/r]`, and the actual supported coherent sheaves in its kernel.

The restriction map is exactly the original exact functor's canonical
small-model K-map. The supported term is the explicit small presentation
`PrincipalSupportedG`, with a proved exact equivalence to the previously
chosen small model of the actual support category (`principalSupportedGEquiv`).
This is not a theorem for arbitrary non-affine schemes, nor does it identify
the support term with coherent sheaves on a closed subscheme without dévissage.
-/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen
open Quillen.CoherentScheme


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.Coherent
variable (R : CommRingCat.{u}) [IsNoetherianRing R] (r : R)

local instance : PreservesFiniteLimits (affinePrincipalRestrictionExact R r).toFunctor :=
  affinePrincipalRestriction_preservesFiniteLimits R r

local instance : PreservesFiniteColimits (affinePrincipalRestrictionExact R r).toFunctor :=
  affinePrincipalRestriction_preservesFiniteColimits R r

local instance : (affinePrincipalRestrictionExact R r).toFunctor.IsLocalization
    (affinePrincipalRestrictionExact R r).toFunctor.kernel.isoModSerre :=
  affinePrincipalRestriction_isLocalization_kernel R r

/-- The canonical G-map of actual principal-open restriction. -/
def principalRestrictionGMap (n : ℕ) :
    AffineG R n →* AffineG (CommRingCat.of (Localization.Away r)) n :=
  (affinePrincipalRestrictionExact R r).smallKMap n

/-- The supported inclusion in the compatible source small model. -/
def principalInclusionGMap (n : ℕ) : PrincipalSupportedG R r n →* AffineG R n :=
  SmallModelGLocalization.inclusionKMap (affinePrincipalRestrictionExact R r) n

/-- The canonical connecting homomorphism into the actual supported term. -/
def principalConnectingHom (n : ℕ) :
    AffineG (CommRingCat.of (Localization.Away r)) (n + 1) →* PrincipalSupportedG R r n :=
  SmallModelGLocalization.connectingHom (affinePrincipalRestrictionExact R r) n

/-- Every exactness position of the actual principal-open connective G-theory
sequence, with its canonical geometric restriction map and surjective G₀ tail. -/
theorem principal_localization_longExact :
    (∀ n, (principalInclusionGMap R r n).range = (principalRestrictionGMap R r n).ker) ∧
    (∀ n, (principalRestrictionGMap R r (n + 1)).range = (principalConnectingHom R r n).ker) ∧
    (∀ n, (principalConnectingHom R r n).range = (principalInclusionGMap R r n).ker) ∧
    Function.Surjective (principalRestrictionGMap R r 0) :=
  SmallModelGLocalization.localization_longExact (affinePrincipalRestrictionExact R r)

/-- The original homotopical G₀ restriction map is surjective. -/
theorem principal_GZero_surjective : Function.Surjective (principalRestrictionGMap R r 0) :=
  SmallModelGLocalization.KZero_surjective (affinePrincipalRestrictionExact R r)

/-- The low-degree tail `G₁(X) → G₁(U) → G₀^Z(X) → G₀(X) → G₀(U) → 0`. -/
theorem principal_localization_GZero_tail :
    (principalRestrictionGMap R r 1).range = (principalConnectingHom R r 0).ker ∧
    (principalConnectingHom R r 0).range = (principalInclusionGMap R r 0).ker ∧
    (principalInclusionGMap R r 0).range = (principalRestrictionGMap R r 0).ker ∧
    Function.Surjective (principalRestrictionGMap R r 0) :=
  ⟨(principal_localization_longExact R r).2.1 0,
    (principal_localization_longExact R r).2.2.1 0,
    (principal_localization_longExact R r).1 0, principal_GZero_surjective R r⟩

end AlgebraicGeometry.Scheme.Modules.Coherent
