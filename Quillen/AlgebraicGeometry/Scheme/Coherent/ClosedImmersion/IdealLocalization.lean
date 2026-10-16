/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.Algebra.Group.Hom.Exact

public import Aglib.AlgebraicGeometry.Modules.Coherent.Restriction
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Restriction
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Basic
public import Quillen.AlgebraicGeometry.Scheme.Coherent.ClosedImmersion.IdealDevissage

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ClosedImmersion
public import Aglib.AlgebraicGeometry.Modules.Coherent.Localization.Equivalence
/-!
# Geometric affine closed–open localization for public scheme G-theory

For i : Spec(R/I) → Spec R and the open complement j, this is the genuine
connective G-theory sequence with canonical actual sheaf pushforward i_*
and canonical actual restriction j*. The supported comparison is proved by
finite-image dévissage. All groups are the public upper-universe G-groups.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Coherent


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.Ideal

variable (R : CommRingCat.{u}) [IsNoetherianRing R] (I : Ideal R)

local instance : PreservesFiniteLimits (coherentRestrictionExact (openMap R I)).toFunctor :=
  finiteTypeSheavesRestriction_preservesFiniteLimits (openMap R I)

local instance : PreservesFiniteColimits (coherentRestrictionExact (openMap R I)).toFunctor :=
  finiteTypeSheavesRestriction_preservesFiniteColimits (openMap R I)

local instance : (coherentRestrictionExact (openMap R I)).toFunctor.IsLocalization
    (coherentRestrictionExact (openMap R I)).toFunctor.kernel.isoModSerre :=
  finiteTypeSheavesRestriction_isLocalization_kernel (openMap R I)

/-- Actual closed-scheme G-theory agrees with the public supported G-group,
by the proved geometric dévissage and exact small-presentation comparisons. -/
def closedSupportedGEquiv (n : ℕ) :
    AlgebraicGeometry.Scheme.Modules.Coherent.G (Spec
      (Pushforward.ClosedImmersion.Ideal.closedRing R I)) n ≃* SupportedG (openMap R
      I) n :=
  (closedSupportGEquiv R I n).trans (coherentGlobalSupportedGEquiv (openMap R I) n).symm

/-- The public supported comparison retains the original actual closed
pushforward map. -/
theorem closedSupportedGEquiv_pushforward (n : ℕ) :
    (globalInclusionGMap (openMap R I) n).comp (closedSupportedGEquiv R I n).toMonoidHom =
      coherentPushforwardGMap R I n := by
  ext x
  change SmallModelGLocalization.inclusionKMap.{u+1}
      (coherentRestrictionExact (openMap R I)) n
      (coherentGlobalSupportedGEquiv (openMap R I) n
        ((coherentGlobalSupportedGEquiv (openMap R I) n).symm (closedSupportGEquiv R I n x))) = _
  rw [MulEquiv.apply_symm_apply]
  exact DFunLike.congr_fun (closedSupportGEquiv_pushforward R I n) x

/-- The boundary into G-theory of the actual affine closed subscheme. -/
def closedConnectingHom (n : ℕ) :
    AlgebraicGeometry.Scheme.Modules.Coherent.G (openComplement R I).toScheme (n + 1) →*
      AlgebraicGeometry.Scheme.Modules.Coherent.G (Spec
        (Pushforward.ClosedImmersion.Ideal.closedRing R I)) n :=
  (closedSupportedGEquiv R I n).symm.toMonoidHom.comp (globalConnectingHom (openMap R I) n)

/-- Exactness at G_n(Spec R), with canonical actual i_* and j*. -/
theorem pushforward_range_eq_restriction_ker (n : ℕ) :
    (coherentPushforwardGMap R I n).range = (restrictionGMap (openMap R I) n).ker := by
  apply MonoidHom.range_eq_ker_of_equivalences
    (coherentPushforwardGMap R I n) (restrictionGMap (openMap R I) n)
    (globalInclusionGMap (openMap R I) n) (restrictionGMap (openMap R I) n)
    (closedSupportedGEquiv R I n) (MulEquiv.refl _) (MulEquiv.refl _)
  · intro a
    exact (DFunLike.congr_fun (closedSupportedGEquiv_pushforward R I n) a).symm
  · intro b; rfl
  · exact global_inclusion_range_eq_restriction_ker (openMap R I) n

/-- Exactness at G_(n+1) of the actual open complement. -/
theorem restriction_range_eq_closedConnecting_ker (n : ℕ) :
    (restrictionGMap (openMap R I) (n + 1)).range = (closedConnectingHom R I n).ker := by
  apply MonoidHom.range_eq_ker_of_equivalences
    (restrictionGMap (openMap R I) (n + 1)) (closedConnectingHom R I n)
    (restrictionGMap (openMap R I) (n + 1)) (globalConnectingHom (openMap R I) n)
    (MulEquiv.refl _) (MulEquiv.refl _) (closedSupportedGEquiv R I n)
  · intro a; rfl
  · intro b
    exact (closedSupportedGEquiv R I n).apply_symm_apply _
  · exact global_restriction_range_eq_connecting_ker (openMap R I) n

/-- Exactness at G_n of the actual affine closed subscheme. -/
theorem closedConnecting_range_eq_pushforward_ker (n : ℕ) :
    (closedConnectingHom R I n).range = (coherentPushforwardGMap R I n).ker := by
  apply MonoidHom.range_eq_ker_of_equivalences
    (closedConnectingHom R I n) (coherentPushforwardGMap R I n)
    (globalConnectingHom (openMap R I) n) (globalInclusionGMap (openMap R I) n)
    (MulEquiv.refl _) (closedSupportedGEquiv R I n) (MulEquiv.refl _)
  · intro a
    exact (closedSupportedGEquiv R I n).apply_symm_apply _
  · intro b
    exact (DFunLike.congr_fun (closedSupportedGEquiv_pushforward R I n) b).symm
  · exact global_connecting_range_eq_inclusion_ker (openMap R I) n

/-- The full affine closed–open connective G-theory localization sequence
on actual scheme G-groups, with genuine i_*, j*, and the surjective G₀ tail. -/
theorem affine_closed_open_longExact :
    (∀ n, (coherentPushforwardGMap R I n).range = (restrictionGMap (openMap R I) n).ker) ∧
    (∀ n, (restrictionGMap (openMap R I) (n + 1)).range = (closedConnectingHom R I n).ker) ∧
    (∀ n, (closedConnectingHom R I n).range = (coherentPushforwardGMap R I n).ker) ∧
    Function.Surjective (restrictionGMap (openMap R I) 0) :=
  ⟨pushforward_range_eq_restriction_ker R I,
    restriction_range_eq_closedConnecting_ker R I,
    closedConnecting_range_eq_pushforward_ker R I,
    global_GZero_surjective (openMap R I)⟩

/-- The low-degree tail G₁(X) → G₁(U) → G₀(Z) → G₀(X) → G₀(U) → 0. -/
theorem affine_closed_open_GZero_tail :
    (restrictionGMap (openMap R I) 1).range = (closedConnectingHom R I 0).ker ∧
    (closedConnectingHom R I 0).range = (coherentPushforwardGMap R I 0).ker ∧
    (coherentPushforwardGMap R I 0).range = (restrictionGMap (openMap R I) 0).ker ∧
    Function.Surjective (restrictionGMap (openMap R I) 0) :=
  ⟨restriction_range_eq_closedConnecting_ker R I 0,
    closedConnecting_range_eq_pushforward_ker R I 0,
    pushforward_range_eq_restriction_ker R I 0,
    global_GZero_surjective (openMap R I)⟩

end AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.Ideal
