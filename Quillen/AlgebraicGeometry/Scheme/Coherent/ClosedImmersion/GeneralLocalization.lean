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
public import Quillen.AlgebraicGeometry.Scheme.Coherent.ClosedImmersion.GeneralDevissage
public import Quillen.Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.ClosedImmersion.Annihilator
public import Quillen.Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.ClosedImmersion.AffineIdealKernel
public import Aglib.AlgebraicGeometry.Morphisms.ClosedImmersion.Noetherian
public import Aglib.AlgebraicGeometry.Modules.Coherent.Localization.Equivalence

/-!
# Geometric closed–open localization for public scheme G-theory

For a closed immersion i : Z → X into a noetherian scheme and its open complement j, this is the
  genuine
connective G-theory sequence with canonical actual sheaf pushforward i_*
and canonical actual restriction j*. The supported comparison is proved by
ideal-kernel dévissage. All groups are the public upper-universe G-groups.
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

namespace AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion

variable {Z X : Scheme.{u}} [IsLocallyNoetherian Z] [IsNoetherian X]
  (i : Z ⟶ X) [IsClosedImmersion i]

local instance : PreservesFiniteLimits (coherentRestrictionExact (openMap i)).toFunctor :=
  finiteTypeSheavesRestriction_preservesFiniteLimits (openMap i)

local instance : PreservesFiniteColimits (coherentRestrictionExact (openMap i)).toFunctor :=
  finiteTypeSheavesRestriction_preservesFiniteColimits (openMap i)

local instance : (coherentRestrictionExact (openMap i)).toFunctor.IsLocalization
    (coherentRestrictionExact (openMap i)).toFunctor.kernel.isoModSerre :=
  finiteTypeSheavesRestriction_isLocalization_kernel (openMap i)

/-- Actual closed-scheme G-theory agrees with the public supported G-group,
by the proved geometric dévissage and exact small-presentation comparisons. -/
def closedSupportedGEquiv (n : ℕ) :
    AlgebraicGeometry.Scheme.Modules.Coherent.G Z n ≃* SupportedG (openMap i) n :=
  (closedSupportGEquiv i n).trans (coherentGlobalSupportedGEquiv (openMap i) n).symm

/-- The public supported comparison retains the original actual closed
pushforward map. -/
theorem closedSupportedGEquiv_pushforward (n : ℕ) :
    (globalInclusionGMap (openMap i) n).comp (closedSupportedGEquiv i n).toMonoidHom =
      coherentPushforwardGMap i n := by
  ext x
  change SmallModelGLocalization.inclusionKMap.{u+1}
      (coherentRestrictionExact (openMap i)) n
      (coherentGlobalSupportedGEquiv (openMap i) n
        ((coherentGlobalSupportedGEquiv (openMap i) n).symm (closedSupportGEquiv i n x))) = _
  rw [MulEquiv.apply_symm_apply]
  exact DFunLike.congr_fun (closedSupportGEquiv_pushforward i n) x

/-- The boundary into G-theory of the actual closed subscheme. -/
def closedConnectingHom (n : ℕ) :
    AlgebraicGeometry.Scheme.Modules.Coherent.G (openComplement i).toScheme (n + 1) →*
      AlgebraicGeometry.Scheme.Modules.Coherent.G Z n :=
  (closedSupportedGEquiv i n).symm.toMonoidHom.comp (globalConnectingHom (openMap i) n)

/-- Exactness at G_n(X), with canonical actual i_* and j*. -/
theorem pushforward_range_eq_restriction_ker (n : ℕ) :
    (coherentPushforwardGMap i n).range = (restrictionGMap (openMap i) n).ker := by
  apply MonoidHom.range_eq_ker_of_equivalences
    (coherentPushforwardGMap i n) (restrictionGMap (openMap i) n)
    (globalInclusionGMap (openMap i) n) (restrictionGMap (openMap i) n)
    (closedSupportedGEquiv i n) (MulEquiv.refl _) (MulEquiv.refl _)
  · intro a
    exact (DFunLike.congr_fun (closedSupportedGEquiv_pushforward i n) a).symm
  · intro b; rfl
  · exact global_inclusion_range_eq_restriction_ker (openMap i) n

/-- Exactness at G_(n+1) of the actual open complement. -/
theorem restriction_range_eq_closedConnecting_ker (n : ℕ) :
    (restrictionGMap (openMap i) (n + 1)).range = (closedConnectingHom i n).ker := by
  apply MonoidHom.range_eq_ker_of_equivalences
    (restrictionGMap (openMap i) (n + 1)) (closedConnectingHom i n)
    (restrictionGMap (openMap i) (n + 1)) (globalConnectingHom (openMap i) n)
    (MulEquiv.refl _) (MulEquiv.refl _) (closedSupportedGEquiv i n)
  · intro a; rfl
  · intro b
    exact (closedSupportedGEquiv i n).apply_symm_apply _
  · exact global_restriction_range_eq_connecting_ker (openMap i) n

/-- Exactness at G_n of the actual closed subscheme. -/
theorem closedConnecting_range_eq_pushforward_ker (n : ℕ) :
    (closedConnectingHom i n).range = (coherentPushforwardGMap i n).ker := by
  apply MonoidHom.range_eq_ker_of_equivalences
    (closedConnectingHom i n) (coherentPushforwardGMap i n)
    (globalConnectingHom (openMap i) n) (globalInclusionGMap (openMap i) n)
    (MulEquiv.refl _) (closedSupportedGEquiv i n) (MulEquiv.refl _)
  · intro a
    exact (closedSupportedGEquiv i n).apply_symm_apply _
  · intro b
    exact (DFunLike.congr_fun (closedSupportedGEquiv_pushforward i n) b).symm
  · exact global_connecting_range_eq_inclusion_ker (openMap i) n

/-- The full closed–open connective G-theory localization sequence
on actual scheme G-groups, with genuine i_*, j*, and the surjective G₀ tail. -/
theorem closed_open_longExact :
    (∀ n, (coherentPushforwardGMap i n).range = (restrictionGMap (openMap i) n).ker) ∧
    (∀ n, (restrictionGMap (openMap i) (n + 1)).range = (closedConnectingHom i n).ker) ∧
    (∀ n, (closedConnectingHom i n).range = (coherentPushforwardGMap i n).ker) ∧
    Function.Surjective (restrictionGMap (openMap i) 0) :=
  ⟨pushforward_range_eq_restriction_ker i,
    restriction_range_eq_closedConnecting_ker i,
    closedConnecting_range_eq_pushforward_ker i,
    global_GZero_surjective (openMap i)⟩

/-- The low-degree tail G₁(X) → G₁(U) → G₀(Z) → G₀(X) → G₀(U) → 0. -/
theorem closed_open_GZero_tail :
    (restrictionGMap (openMap i) 1).range = (closedConnectingHom i 0).ker ∧
    (closedConnectingHom i 0).range = (coherentPushforwardGMap i 0).ker ∧
    (coherentPushforwardGMap i 0).range = (restrictionGMap (openMap i) 0).ker ∧
    Function.Surjective (restrictionGMap (openMap i) 0) :=
  ⟨restriction_range_eq_closedConnecting_ker i 0,
    closedConnecting_range_eq_pushforward_ker i 0,
    pushforward_range_eq_restriction_ker i 0,
    global_GZero_surjective (openMap i)⟩

end AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion
