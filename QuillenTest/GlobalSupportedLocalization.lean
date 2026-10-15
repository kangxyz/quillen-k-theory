/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.GlobalLocalization
public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.RestrictionComparison

/-! # Original-map consumers of the qcqs supported connective endpoint -/
@[expose] public section

open Quillen.PerfectComplexes


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
namespace QuillenTest.GlobalSupportedLocalization

open Quillen
open PerfectComplexes
variable {U X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
  (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens) (hT : IsCompact (T : Set X))

include hT in
/-- Every positive original supported target class has one exact relative lift. -/
theorem original_positive_unique_preimage (n : ℕ)
    (y : PerfectSupportedK (j ⁻¹ᵁ T).ι (n+1)) :
    ∃! x : PerfectSupportedOpenK j T (n+1), perfectSupportedOpenKRestrict j T (n+1) x = y := by
  have hb := qcqs_perfectSupportedOpenKRestrict_succ_bijective j T hT n
  obtain ⟨x, hx⟩ := hb.surjective y
  exact ⟨x, hx, fun z hz => hb.injective (hz.trans hx.symm)⟩

include hT in
/-- The honest K0 endpoint is exactly the actual global supported image. -/
theorem original_KZero_unique_iff (y : PerfectSupportedK (j ⁻¹ᵁ T).ι 0) :
    (∃! x : PerfectSupportedOpenK j T 0, perfectSupportedOpenKRestrict j T 0 x = y) ↔
      y ∈ (perfectSupportedKRestrict j T 0).range := by
  constructor
  · rintro ⟨x, rfl, _⟩
    rw [← range_perfectSupportedOpenKRestrict_zero j T]
    exact ⟨x, rfl⟩
  · intro hy
    let y' : PerfectSupportedOpenKZeroImage j T := ⟨y, hy⟩
    let x := (qcqsPerfectSupportedOpenKZeroImageEquiv j T hT).symm y'
    have hx : perfectSupportedOpenKRestrict j T 0 x = y :=
      congrArg Subtype.val ((qcqsPerfectSupportedOpenKZeroImageEquiv j T hT).apply_symm_apply y')
    exact ⟨x, hx, fun z hz => qcqs_perfectSupportedOpenKRestrict_zero_injective j T hT (hz.trans
      hx.symm)⟩

/-- All three exact tail positions retain the actual existing public pair map. -/
theorem original_public_zero_tail :
    (perfectSupportedKPullback (qcSupportRestrictionPair j T) 1).range =
      (qcqsPerfectSupportedConnectingHom j T hT 0).ker ∧
    (qcqsPerfectSupportedConnectingHom j T hT 0).range =
      (perfectSupportedUnionKMap j T 0).ker ∧
    (perfectSupportedUnionKMap j T 0).range =
      (perfectSupportedKPullback (qcSupportRestrictionPair j T) 0).ker := by
  simpa only [perfectSupportedKRestrict_eq_pullback] using qcqsPerfectSupported_zeroTail j T hT

/-- A genuine degree-zero kernel class has an original K1 boundary preimage. -/
theorem original_KZero_kernel_boundary (x : PerfectSupportedK (T ⊔ j.opensRange).ι 0)
    (hx : perfectSupportedUnionKMap j T 0 x = 1) :
    ∃ y : PerfectSupportedK (j ⁻¹ᵁ T).ι 1,
      qcqsPerfectSupportedConnectingHom j T hT 0 y = x := by
  have hm : x ∈ (perfectSupportedUnionKMap j T 0).ker := hx
  rw [← range_qcqsPerfectSupportedConnectingHom_eq_ker_perfectSupportedUnionKMap j T hT 0] at hm
  exact hm

/-- The original inverse endpoint respects actual support-forgetting. -/
theorem original_inverse_forget (n : ℕ) (x : PerfectSupportedK (j ⁻¹ᵁ T).ι (n+1)) :
    perfectSupportedOpenKForget j T (n+1) ((qcqsPerfectSupportedOpenKEquiv j T hT n).symm x) =
      (qcqsPerfectOpenKEquiv j n).symm (perfectSupportedKMap (j ⁻¹ᵁ T).ι (n+1) x) :=
  qcqsPerfectSupportedOpenKEquiv_symm_forget j T hT n x

/-- Forgetting auxiliary support retains exactly the original K1-to-K0 boundary. -/
theorem original_boundary_forget (x : PerfectSupportedK (j ⁻¹ᵁ T).ι 1) :
    perfectSupportedUnionForgetKMap j T 0 (qcqsPerfectSupportedConnectingHom j T hT 0 x) =
      qcqsPerfectConnectingHom j 0 (perfectSupportedKMap (j ⁻¹ᵁ T).ι 1 x) :=
  DFunLike.congr_fun (qcqsPerfectSupportedConnectingHom_forget j T hT 0) x

omit [QuasiSeparatedSpace X] in
/-- Full-target K0 surjectivity is exactly the original public map's obstruction. -/
theorem original_KZero_surjective_iff :
    Function.Surjective (perfectSupportedOpenKRestrict j T 0) ↔
      Function.Surjective (perfectSupportedKPullback (qcSupportRestrictionPair j T) 0) := by
  rw [perfectSupportedOpenKRestrict_zero_surjective_iff, perfectSupportedKRestrict_eq_pullback]
  rfl

/-- Empty source and empty auxiliary open are allowed with the literal inverse law. -/
theorem empty_open_original_inverse (R : CommRingCat.{u}) (n : ℕ)
    (x : PerfectSupportedOpenK (⊥ : (Spec R).Opens).ι (⊥ : (Spec R).Opens) (n+1)) :
    let : CompactSpace (⊥ : (Spec R).Opens).toScheme :=
      isCompact_iff_compactSpace.mp isCompact_empty
    (qcqsPerfectSupportedOpenKEquiv (⊥ : (Spec R).Opens).ι (⊥ : (Spec R).Opens)
      isCompact_empty n).symm
      (perfectSupportedOpenKRestrict (⊥ : (Spec R).Opens).ι (⊥ : (Spec R).Opens) (n+1) x) = x := by
  let : CompactSpace (⊥ : (Spec R).Opens).toScheme :=
    isCompact_iff_compactSpace.mp isCompact_empty
  exact (qcqsPerfectSupportedOpenKEquiv (⊥ : (Spec R).Opens).ι (⊥ : (Spec R).Opens)
    isCompact_empty n).symm_apply_apply x

end QuillenTest.GlobalSupportedLocalization
