/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.PerfectComplexes.Affine.PrincipalPerfectCofinality

/-! # Original principal connective localization sequence

The actual relative-open boundary is transported through the proved positive
principal endpoint equivalence. All original support-forgetting and restriction
maps remain unchanged. The degree-zero tail is exact without asserting
surjectivity onto K-zero of the open.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes.Affine
variable (R : CommRingCat.{u}) (r : R)

/-- The original principal relative endpoint is injective in every connective degree. -/
theorem principal_perfectOpenKRestrict_injective (n : ℕ) :
    Function.Injective (perfectOpenKRestrict (CoherentScheme.principalOpen R r) n) := by
  cases n with
  | zero => exact principal_perfectOpenKRestrict_zero_injective R r
  | succ n => exact (principal_perfectOpenKRestrict_succ_bijective R r n).injective

/-- Genuine supported boundary from original perfect K-theory of the principal open. -/
def principalPerfectConnectingHom (n : ℕ) :
    PerfectK (Spec (.of (Localization.Away r))) (n + 1) →*
      PerfectSupportedK (CoherentScheme.principalOpen R r) n :=
  (perfectOpenConnectingHom (CoherentScheme.principalOpen R r) n).comp
    (principalPerfectOpenKEquiv R r n).symm.toMonoidHom

/-- The transported boundary retains the entire original relative boundary homomorphism. -/
theorem principalPerfectConnectingHom_comp_relative (n : ℕ) :
    (principalPerfectConnectingHom R r n).comp
      (perfectOpenKRestrict (CoherentScheme.principalOpen R r) (n + 1)) =
    perfectOpenConnectingHom (CoherentScheme.principalOpen R r) n := by
  ext a
  change perfectOpenConnectingHom (CoherentScheme.principalOpen R r) n
    ((principalPerfectOpenKEquiv R r n).symm ((principalPerfectOpenKEquiv R r n) a)) = _
  rw [MulEquiv.symm_apply_apply]

/-- Exactness at original perfect K-theory on the affine base, including degree zero. -/
theorem range_perfectSupportedKMap_eq_ker_principal_perfectKRestrict (n : ℕ) :
    (perfectSupportedKMap (CoherentScheme.principalOpen R r) n).range =
      (perfectKRestrict (CoherentScheme.principalOpen R r) n).ker := by
  rw [range_perfectSupportedKMap_eq_ker_perfectOpenKMap]
  ext x
  change perfectOpenKMap (CoherentScheme.principalOpen R r) n x = 1 ↔
    perfectKRestrict (CoherentScheme.principalOpen R r) n x = 1
  have he := DFunLike.congr_fun
    (perfectOpenKRestrict_comp_perfectOpenKMap (CoherentScheme.principalOpen R r) n) x
  constructor
  · intro hx
    rw [← he, MonoidHom.comp_apply, hx, map_one]
  · intro hx
    apply principal_perfectOpenKRestrict_injective R r n
    exact he.trans (hx.trans (map_one _).symm)

/-- The new boundary has exactly the original relative boundary image. -/
theorem range_principalPerfectConnectingHom (n : ℕ) :
    (principalPerfectConnectingHom R r n).range =
      (perfectOpenConnectingHom (CoherentScheme.principalOpen R r) n).range := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨(principalPerfectOpenKEquiv R r n).symm a, rfl⟩
  · rintro ⟨a, rfl⟩
    refine ⟨principalPerfectOpenKEquiv R r n a, ?_⟩
    exact DFunLike.congr_fun (principalPerfectConnectingHom_comp_relative R r n) a

/-- Exactness at original supported perfect K-theory, including its degree-zero group. -/
theorem range_principalPerfectConnectingHom_eq_ker_perfectSupportedKMap (n : ℕ) :
    (principalPerfectConnectingHom R r n).range =
      (perfectSupportedKMap (CoherentScheme.principalOpen R r) n).ker := by
  rw [range_principalPerfectConnectingHom,
    range_perfectOpenConnectingHom_eq_ker_perfectSupportedKMap]

/-- Exactness at positive original perfect K-theory of the principal open. -/
theorem range_principal_perfectKRestrict_eq_ker_principalPerfectConnectingHom (n : ℕ) :
    (perfectKRestrict (CoherentScheme.principalOpen R r) (n + 1)).range =
      (principalPerfectConnectingHom R r n).ker := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    change principalPerfectConnectingHom R r n
      (perfectKRestrict (CoherentScheme.principalOpen R r) (n + 1) a) = 1
    rw [← DFunLike.congr_fun
      (perfectOpenKRestrict_comp_perfectOpenKMap (CoherentScheme.principalOpen R r) (n + 1)) a]
    change ((principalPerfectConnectingHom R r n).comp
      (perfectOpenKRestrict (CoherentScheme.principalOpen R r) (n + 1)))
      (perfectOpenKMap (CoherentScheme.principalOpen R r) (n + 1) a) = 1
    rw [principalPerfectConnectingHom_comp_relative]
    have hm : perfectOpenKMap (CoherentScheme.principalOpen R r) (n + 1) a ∈
        (perfectOpenKMap (CoherentScheme.principalOpen R r) (n + 1)).range := ⟨a, rfl⟩
    rw [range_perfectOpenKMap_eq_ker_perfectOpenConnectingHom] at hm
    exact hm
  · intro hx
    have hm : (principalPerfectOpenKEquiv R r n).symm x ∈
        (perfectOpenConnectingHom (CoherentScheme.principalOpen R r) n).ker := hx
    rw [← range_perfectOpenKMap_eq_ker_perfectOpenConnectingHom] at hm
    obtain ⟨a, ha⟩ := hm
    refine ⟨a, ?_⟩
    rw [← DFunLike.congr_fun
      (perfectOpenKRestrict_comp_perfectOpenKMap (CoherentScheme.principalOpen R r) (n + 1)) a]
    change principalPerfectOpenKEquiv R r n
      (perfectOpenKMap (CoherentScheme.principalOpen R r) (n + 1) a) = x
    rw [ha, MulEquiv.apply_symm_apply]

/-- All recurring positions of the actual principal connective localization sequence. -/
theorem principalPerfect_positiveLongExactSequence (n : ℕ) :
    (perfectKRestrict (CoherentScheme.principalOpen R r) (n + 1)).range =
      (principalPerfectConnectingHom R r n).ker ∧
    (principalPerfectConnectingHom R r n).range =
      (perfectSupportedKMap (CoherentScheme.principalOpen R r) n).ker ∧
    (perfectSupportedKMap (CoherentScheme.principalOpen R r) n).range =
      (perfectKRestrict (CoherentScheme.principalOpen R r) n).ker :=
  ⟨range_principal_perfectKRestrict_eq_ker_principalPerfectConnectingHom R r n,
    range_principalPerfectConnectingHom_eq_ker_perfectSupportedKMap R r n,
    range_perfectSupportedKMap_eq_ker_principal_perfectKRestrict R r n⟩

/-- The actual K₁(open) → K₀(support) → K₀(base) → K₀(open) exact tail. -/
theorem principalPerfect_zeroTail :
    (perfectKRestrict (CoherentScheme.principalOpen R r) 1).range =
      (principalPerfectConnectingHom R r 0).ker ∧
    (principalPerfectConnectingHom R r 0).range =
      (perfectSupportedKMap (CoherentScheme.principalOpen R r) 0).ker ∧
    (perfectSupportedKMap (CoherentScheme.principalOpen R r) 0).range =
      (perfectKRestrict (CoherentScheme.principalOpen R r) 0).ker :=
  principalPerfect_positiveLongExactSequence R r 0

end Quillen.PerfectComplexes.Affine
