/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.CategoryTheory.SmallModel.Exact
public import Aglib.AlgebraicGeometry.Modules.Coherent.Restriction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeRestriction
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Restriction
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Basic
public import Quillen.AlgebraicGeometry.Scheme.Coherent.PrincipalSupport
public import Quillen.GTheory.SmallModelLocalization
public import Aglib.Algebra.Group.Subgroup.Ker
public import Aglib.AlgebraicGeometry.Modules.Coherent.Localization.Principal

/-!
# Principal-open localization for the public global scheme G-theory

The actual restriction of global coherent sheaves is a proved Serre
localization. Applying the small-model theorem in universe `u+1` gives the
connective localization sequence for the public `G` and `SupportedG`
definitions. The middle-to-open map is exactly `restrictionGMap`.

The support maps use the proved exact comparison with the compatible
small support presentation. No equality between different-universe
realizations is needed, and no non-affine localization theorem is asserted.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Coherent


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open Quillen



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.Coherent

variable (R : CommRingCat.{u}) [IsNoetherianRing R] (r : R)

local instance : PreservesFiniteLimits (coherentRestrictionExact (principalOpen R r)).toFunctor :=
  finiteTypeSheavesRestriction_preservesFiniteLimits (principalOpen R r)

local instance : PreservesFiniteColimits (coherentRestrictionExact (principalOpen R r)).toFunctor :=
  finiteTypeSheavesRestriction_preservesFiniteColimits (principalOpen R r)

local instance : (coherentRestrictionExact (principalOpen R r)).toFunctor.IsLocalization
    (coherentRestrictionExact (principalOpen R r)).toFunctor.kernel.isoModSerre :=
  coherentPrincipalRestriction_isLocalization_kernel R r

/-- The supported inclusion for the actual public global supported G-group,
using its canonical exact-presentation comparison. -/
def globalPrincipalInclusionGMap (n : ℕ) :
    SupportedG (principalOpen R r) n →* G (Spec R) n :=
  (SmallModelGLocalization.inclusionKMap.{u+1} (coherentRestrictionExact (principalOpen R r))
    n).comp
    (coherentPrincipalSupportedGEquiv R r n).toMonoidHom

/-- The connecting homomorphism into the actual public supported G-group. -/
def globalPrincipalConnectingHom (n : ℕ) :
    G (Spec (CommRingCat.of (Localization.Away r))) (n + 1) →*
      SupportedG (principalOpen R r) n :=
  (coherentPrincipalSupportedGEquiv R r n).symm.toMonoidHom.comp
    (SmallModelGLocalization.connectingHom.{u+1} (coherentRestrictionExact (principalOpen R r)) n)

/-- Exactness at the public global G-group of the ambient affine scheme. -/
theorem globalPrincipal_inclusion_range_eq_restriction_ker (n : ℕ) :
    (globalPrincipalInclusionGMap R r n).range =
      (restrictionGMap (principalOpen R r) n).ker := by
  apply MonoidHom.range_eq_ker_of_equiv
    (globalPrincipalInclusionGMap R r n) (restrictionGMap (principalOpen R r) n)
    (SmallModelGLocalization.inclusionKMap.{u+1} (coherentRestrictionExact (principalOpen R r)) n)
    (CategoryTheory.ExactCategory.ExactFunctor.smallKMap.{u+1} (coherentRestrictionExact
      (principalOpen R r)) n)
    (coherentPrincipalSupportedGEquiv R r n) (MulEquiv.refl _) (MulEquiv.refl _)
  · intro a; rfl
  · intro b; rfl
  · exact SmallModelGLocalization.inclusion_range_eq_KMap_ker.{u+1}
      (coherentRestrictionExact (principalOpen R r)) n

/-- Exactness at the public global G-group of the principal open. -/
theorem globalPrincipal_restriction_range_eq_connecting_ker (n : ℕ) :
    (restrictionGMap (principalOpen R r) (n + 1)).range =
      (globalPrincipalConnectingHom R r n).ker := by
  apply MonoidHom.range_eq_ker_of_equiv
    (restrictionGMap (principalOpen R r) (n + 1)) (globalPrincipalConnectingHom R r n)
    (CategoryTheory.ExactCategory.ExactFunctor.smallKMap.{u+1} (coherentRestrictionExact
      (principalOpen R r)) (n + 1))
    (SmallModelGLocalization.connectingHom.{u+1} (coherentRestrictionExact (principalOpen R r)) n)
    (MulEquiv.refl _) (MulEquiv.refl _) (coherentPrincipalSupportedGEquiv R r n)
  · intro a; rfl
  · intro b
    exact (coherentPrincipalSupportedGEquiv R r n).apply_symm_apply _
  · exact SmallModelGLocalization.KMap_range_eq_connecting_ker.{u+1}
      (coherentRestrictionExact (principalOpen R r)) n

/-- Exactness at the actual supported global G-group. -/
theorem globalPrincipal_connecting_range_eq_inclusion_ker (n : ℕ) :
    (globalPrincipalConnectingHom R r n).range =
      (globalPrincipalInclusionGMap R r n).ker := by
  apply MonoidHom.range_eq_ker_of_equiv
    (globalPrincipalConnectingHom R r n) (globalPrincipalInclusionGMap R r n)
    (SmallModelGLocalization.connectingHom.{u+1} (coherentRestrictionExact (principalOpen R r)) n)
    (SmallModelGLocalization.inclusionKMap.{u+1} (coherentRestrictionExact (principalOpen R r)) n)
    (MulEquiv.refl _) (coherentPrincipalSupportedGEquiv R r n) (MulEquiv.refl _)
  · intro a
    exact (coherentPrincipalSupportedGEquiv R r n).apply_symm_apply _
  · intro b; rfl
  · exact SmallModelGLocalization.connecting_range_eq_inclusion_ker.{u+1}
      (coherentRestrictionExact (principalOpen R r)) n

/-- The public global G-zero restriction map is surjective. -/
theorem globalPrincipal_GZero_surjective :
    Function.Surjective (restrictionGMap (principalOpen R r) 0) :=
  SmallModelGLocalization.KZero_surjective.{u+1} (coherentRestrictionExact (principalOpen R r))

/-- The complete principal-open connective localization sequence for the
public global scheme G-groups and actual supported coherent sheaves. -/
theorem global_principal_localization_longExact :
    (∀ n, (globalPrincipalInclusionGMap R r n).range =
      (restrictionGMap (principalOpen R r) n).ker) ∧
    (∀ n, (restrictionGMap (principalOpen R r) (n + 1)).range =
      (globalPrincipalConnectingHom R r n).ker) ∧
    (∀ n, (globalPrincipalConnectingHom R r n).range =
      (globalPrincipalInclusionGMap R r n).ker) ∧
    Function.Surjective (restrictionGMap (principalOpen R r) 0) :=
  ⟨globalPrincipal_inclusion_range_eq_restriction_ker R r,
    globalPrincipal_restriction_range_eq_connecting_ker R r,
    globalPrincipal_connecting_range_eq_inclusion_ker R r,
    globalPrincipal_GZero_surjective R r⟩

/-- The low-degree public global localization tail. -/
theorem global_principal_localization_GZero_tail :
    (restrictionGMap (principalOpen R r) 1).range =
      (globalPrincipalConnectingHom R r 0).ker ∧
    (globalPrincipalConnectingHom R r 0).range =
      (globalPrincipalInclusionGMap R r 0).ker ∧
    (globalPrincipalInclusionGMap R r 0).range =
      (restrictionGMap (principalOpen R r) 0).ker ∧
    Function.Surjective (restrictionGMap (principalOpen R r) 0) :=
  ⟨globalPrincipal_restriction_range_eq_connecting_ker R r 0,
    globalPrincipal_connecting_range_eq_inclusion_ker R r 0,
    globalPrincipal_inclusion_range_eq_restriction_ker R r 0,
    globalPrincipal_GZero_surjective R r⟩

end AlgebraicGeometry.Scheme.Modules.Coherent
