/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pushforward
public import Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.ClosedImmersion.IdealPushforward
public import Aglib.AlgebraicGeometry.Modules.Coherent.Restriction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeRestriction
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Restriction
public import Quillen.AlgebraicGeometry.Scheme.Coherent.Basic
public import Quillen.AlgebraicGeometry.Scheme.Coherent.ClosedImmersion.Devissage

/-!
# Geometric principal closed–open localization for public scheme G-theory

For i : Spec(R/(f)) → Spec R and the principal open j, this is the genuine
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

namespace AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.Principal

private theorem exact_transport
    {A B C A' B' C' : Type w}
    [Group A] [Group B] [Group C] [Group A'] [Group B'] [Group C']
    (i : A →* B) (f : B →* C) (i' : A' →* B') (f' : B' →* C')
    (eA : A ≃* A') (eB : B ≃* B') (eC : C ≃* C')
    (hi : ∀ a, eB (i a) = i' (eA a))
    (hf : ∀ b, eC (f b) = f' (eB b))
    (h : i'.range = f'.ker) : i.range = f.ker := by
  ext b
  rw [MonoidHom.mem_range, MonoidHom.mem_ker]
  constructor
  · rintro ⟨a, rfl⟩
    apply eC.injective
    rw [map_one, hf, hi]
    have hx : i' (eA a) ∈ i'.range := ⟨eA a, rfl⟩
    rw [h] at hx
    exact hx
  · intro hb
    have hx : eB b ∈ i'.range := by
      rw [h]
      change f' (eB b) = 1
      rw [← hf, hb, map_one]
    obtain ⟨a, ha⟩ := hx
    refine ⟨eA.symm a, eB.injective ?_⟩
    rw [hi, eA.apply_symm_apply, ha]

variable (R : CommRingCat.{u}) [IsNoetherianRing R] (f : R)

local instance : PreservesFiniteLimits (coherentRestrictionExact (principalOpen R f)).toFunctor :=
  finiteTypeSheavesRestriction_preservesFiniteLimits (principalOpen R f)

local instance : PreservesFiniteColimits (coherentRestrictionExact (principalOpen R f)).toFunctor :=
  finiteTypeSheavesRestriction_preservesFiniteColimits (principalOpen R f)

local instance : (coherentRestrictionExact (principalOpen R f)).toFunctor.IsLocalization
    (coherentRestrictionExact (principalOpen R f)).toFunctor.kernel.isoModSerre :=
  coherentPrincipalRestriction_isLocalization_kernel R f

/-- Actual closed-scheme G-theory agrees with the public supported G-group,
by the proved geometric dévissage and exact small-presentation comparisons. -/
def closedSupportedGEquiv (n : ℕ) :
    AlgebraicGeometry.Scheme.Modules.Coherent.G (Spec
      (AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.Ideal.closedRing R
      (Ideal.span {f}))) n ≃* SupportedG
      (principalOpen R f) n :=
  (closedSupportGEquiv R f n).trans (coherentPrincipalSupportedGEquiv R f n).symm

/-- The public supported comparison retains the original actual closed
pushforward map. -/
theorem closedSupportedGEquiv_pushforward (n : ℕ) :
    (globalPrincipalInclusionGMap R f n).comp (closedSupportedGEquiv R f n).toMonoidHom =
      coherentPushforwardGMap R f n := by
  ext x
  change SmallModelGLocalization.inclusionKMap.{u+1}
      (coherentRestrictionExact (principalOpen R f)) n
      (coherentPrincipalSupportedGEquiv R f n
        ((coherentPrincipalSupportedGEquiv R f n).symm (closedSupportGEquiv R f n x))) = _
  rw [MulEquiv.apply_symm_apply]
  exact DFunLike.congr_fun (closedSupportGEquiv_pushforward R f n) x

/-- The boundary into G-theory of the actual principal closed subscheme. -/
def closedConnectingHom (n : ℕ) :
    AlgebraicGeometry.Scheme.Modules.Coherent.G (Spec (CommRingCat.of (Localization.Away f))) (n +
      1) →*
      AlgebraicGeometry.Scheme.Modules.Coherent.G (Spec
        (AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.Ideal.closedRing R
        (Ideal.span {f}))) n :=
  (closedSupportedGEquiv R f n).symm.toMonoidHom.comp (globalPrincipalConnectingHom R f n)

/-- Exactness at G_n(Spec R), with canonical actual i_* and j*. -/
theorem pushforward_range_eq_restriction_ker (n : ℕ) :
    (coherentPushforwardGMap R f n).range = (restrictionGMap (principalOpen R f) n).ker := by
  apply exact_transport
    (coherentPushforwardGMap R f n) (restrictionGMap (principalOpen R f) n)
    (globalPrincipalInclusionGMap R f n) (restrictionGMap (principalOpen R f) n)
    (closedSupportedGEquiv R f n) (MulEquiv.refl _) (MulEquiv.refl _)
  · intro a
    exact (DFunLike.congr_fun (closedSupportedGEquiv_pushforward R f n) a).symm
  · intro b; rfl
  · exact globalPrincipal_inclusion_range_eq_restriction_ker R f n

/-- Exactness at G_(n+1) of the actual principal open. -/
theorem restriction_range_eq_closedConnecting_ker (n : ℕ) :
    (restrictionGMap (principalOpen R f) (n + 1)).range = (closedConnectingHom R f n).ker := by
  apply exact_transport
    (restrictionGMap (principalOpen R f) (n + 1)) (closedConnectingHom R f n)
    (restrictionGMap (principalOpen R f) (n + 1)) (globalPrincipalConnectingHom R f n)
    (MulEquiv.refl _) (MulEquiv.refl _) (closedSupportedGEquiv R f n)
  · intro a; rfl
  · intro b
    exact (closedSupportedGEquiv R f n).apply_symm_apply _
  · exact globalPrincipal_restriction_range_eq_connecting_ker R f n

/-- Exactness at G_n of the actual principal closed subscheme. -/
theorem closedConnecting_range_eq_pushforward_ker (n : ℕ) :
    (closedConnectingHom R f n).range = (coherentPushforwardGMap R f n).ker := by
  apply exact_transport
    (closedConnectingHom R f n) (coherentPushforwardGMap R f n)
    (globalPrincipalConnectingHom R f n) (globalPrincipalInclusionGMap R f n)
    (MulEquiv.refl _) (closedSupportedGEquiv R f n) (MulEquiv.refl _)
  · intro a
    exact (closedSupportedGEquiv R f n).apply_symm_apply _
  · intro b
    exact (DFunLike.congr_fun (closedSupportedGEquiv_pushforward R f n) b).symm
  · exact globalPrincipal_connecting_range_eq_inclusion_ker R f n

/-- The full principal closed–open connective G-theory localization sequence
on actual scheme G-groups, with genuine i_*, j*, and the surjective G₀ tail. -/
theorem principal_closed_open_longExact :
    (∀ n, (coherentPushforwardGMap R f n).range = (restrictionGMap (principalOpen R f) n).ker) ∧
    (∀ n, (restrictionGMap (principalOpen R f) (n + 1)).range = (closedConnectingHom R f n).ker) ∧
    (∀ n, (closedConnectingHom R f n).range = (coherentPushforwardGMap R f n).ker) ∧
    Function.Surjective (restrictionGMap (principalOpen R f) 0) :=
  ⟨pushforward_range_eq_restriction_ker R f,
    restriction_range_eq_closedConnecting_ker R f,
    closedConnecting_range_eq_pushforward_ker R f,
    globalPrincipal_GZero_surjective R f⟩

/-- The low-degree tail G₁(X) → G₁(U) → G₀(Z) → G₀(X) → G₀(U) → 0. -/
theorem principal_closed_open_GZero_tail :
    (restrictionGMap (principalOpen R f) 1).range = (closedConnectingHom R f 0).ker ∧
    (closedConnectingHom R f 0).range = (coherentPushforwardGMap R f 0).ker ∧
    (coherentPushforwardGMap R f 0).range = (restrictionGMap (principalOpen R f) 0).ker ∧
    Function.Surjective (restrictionGMap (principalOpen R f) 0) :=
  ⟨restriction_range_eq_closedConnecting_ker R f 0,
    closedConnecting_range_eq_pushforward_ker R f 0,
    pushforward_range_eq_restriction_ker R f 0,
    globalPrincipal_GZero_surjective R f⟩

end AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.Principal
