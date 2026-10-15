/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.MayerVietoris
public import Quillen.AlgebraicGeometry.PerfectComplexes.MayerVietoris

/-! # Actual supported Mayer–Vietoris boundary forgets to the original boundary -/
@[expose] public section

open Quillen.Waldhausen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace Quillen.PerfectComplexes.SupportedMayerVietoris
open Waldhausen
variable {V X : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j] (T Z : X.Opens)

/-- Both original support-forgetting routes are the same actual inclusion. -/
lemma union_forget_comp (n : ℕ) :
    (perfectSupportedKMap Z.ι n).comp (perfectSupportedUnionKMap T.ι Z n) =
      (perfectSupportedKMap T.ι n).comp (perfectSupportedUnionForgetKMap T.ι Z n) := by
  unfold perfectSupportedKMap perfectSupportedUnionKMap perfectSupportedUnionForgetKMap
    subcategoryKMap
  rw [Quillen.Waldhausen.KMap_comp_KMap, Quillen.Waldhausen.KMap_comp_KMap]

variable [CompactSpace X] [CompactSpace V]

/-- The literal public fiber map retains auxiliary-support forgetting. -/
lemma fiberMap_forget (n : ℕ) :
    (perfectSupportedUnionForgetKMap (j ⁻¹ᵁ T).ι (j ⁻¹ᵁ Z) n).comp (fiberMap j T Z n) =
      (perfectSupportedKRestrict j T n).comp (perfectSupportedUnionForgetKMap T.ι Z n) := by
  let : IsOpenImmersion (fiberPair j T Z).hom.right := inferInstanceAs (IsOpenImmersion j)
  have he := perfectSupportedKPullback_eq_restrictOfLE _ _ (fiberPair j T Z) n
  change fiberMap j T Z n = _ at he
  rw [he]
  unfold perfectSupportedKRestrictOfLE perfectSupportedUnionForgetKMap perfectSupportedKRestrict
    subcategoryKMap
  rw [Quillen.Waldhausen.KMap_comp_KMap, Quillen.Waldhausen.KMap_comp_KMap]

variable (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ T)

/-- The inverse is forced by the original two excision maps, including at K-zero. -/
lemma fiberEquiv_symm_forget (n : ℕ) :
    (perfectSupportedUnionForgetKMap T.ι Z n).comp (fiberEquiv j T Z hcover n).symm.toMonoidHom =
      (perfectSupportedExcisionKEquiv j T hcover n).symm.toMonoidHom.comp
        (perfectSupportedUnionForgetKMap (j ⁻¹ᵁ T).ι (j ⁻¹ᵁ Z) n) := by
  apply MonoidHom.ext
  intro x
  apply (perfectSupportedExcisionKEquiv j T hcover n).injective
  have h := DFunLike.congr_fun (fiberMap_forget j T Z n) ((fiberEquiv j T Z hcover n).symm x)
  change perfectSupportedUnionForgetKMap (j ⁻¹ᵁ T).ι (j ⁻¹ᵁ Z) n
    ((fiberEquiv j T Z hcover n) ((fiberEquiv j T Z hcover n).symm x)) = _ at h
  rw [MulEquiv.apply_symm_apply] at h
  change perfectSupportedKRestrict j T n
    (perfectSupportedUnionForgetKMap T.ι Z n ((fiberEquiv j T Z hcover n).symm x)) =
      (perfectSupportedExcisionKEquiv j T hcover n)
        ((perfectSupportedExcisionKEquiv j T hcover n).symm _)
  rw [MulEquiv.apply_symm_apply]
  exact h.symm

variable [QuasiSeparatedSpace X] [QuasiSeparatedSpace V]
  [CompactSpace T.toScheme] [CompactSpace (j ⁻¹ᵁ T).toScheme]
  (hZ : IsCompact (Z : Set X))

omit [CompactSpace T.toScheme] in
/-- Original auxiliary-support forgetting takes the entire actual boundary to
ordinary Mayer–Vietoris, with the same sign and the same overlap restriction. -/
lemma connectingHom_forget (n : ℕ) :
    (perfectSupportedKMap Z.ι n).comp (connectingHom j T Z hZ hcover n) =
      (PerfectMayerVietoris.connectingHom j T hcover n).comp
        (perfectSupportedKMap ((j ⁻¹ᵁ T).ι ⁻¹ᵁ (j ⁻¹ᵁ Z)).ι (n+1)) := by
  apply MonoidHom.ext
  intro x
  let δ := qcqsPerfectSupportedConnectingHom (j ⁻¹ᵁ T).ι (j ⁻¹ᵁ Z) (j.isCompact_preimage hZ) n
  have h₁ := DFunLike.congr_fun (union_forget_comp T Z n) ((fiberEquiv j T Z hcover n).symm (δ x))
  have h₂ := DFunLike.congr_fun (fiberEquiv_symm_forget j T Z hcover n) (δ x)
  have h₃ := DFunLike.congr_fun
    (qcqsPerfectSupportedConnectingHom_forget (j ⁻¹ᵁ T).ι (j ⁻¹ᵁ Z) (j.isCompact_preimage hZ) n) x
  simp only [MonoidHom.comp_apply] at h₁ h₂ h₃
  change perfectSupportedKMap Z.ι n
    (perfectSupportedUnionKMap T.ι Z n ((fiberEquiv j T Z hcover n).symm (δ x))) =
      perfectSupportedKMap T.ι n ((perfectSupportedExcisionKEquiv j T hcover n).symm
        (qcqsPerfectConnectingHom (j ⁻¹ᵁ T).ι n
          (perfectSupportedKMap ((j ⁻¹ᵁ T).ι ⁻¹ᵁ (j ⁻¹ᵁ Z)).ι (n+1) x)))
  change perfectSupportedUnionForgetKMap T.ι Z n ((fiberEquiv j T Z hcover n).symm (δ x)) =
    (perfectSupportedExcisionKEquiv j T hcover n).symm
      (perfectSupportedUnionForgetKMap (j ⁻¹ᵁ T).ι (j ⁻¹ᵁ Z) n (δ x)) at h₂
  rw [h₁,h₂]
  rw [h₃]

end Quillen.PerfectComplexes.SupportedMayerVietoris

end

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
namespace Quillen.PerfectComplexes.SupportedMayerVietoris
variable {V X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace V]
  (j : V ⟶ X) [IsOpenImmersion j] (T Z : X.Opens)
  (hT : IsCompact (T : Set X)) (hZ : IsCompact (Z : Set X))
  (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ T)

/-- Forgetting the auxiliary support commutes with the original complete
qcqs Mayer–Vietoris boundary in every connective degree, including K1→K0. -/
theorem qcqsConnectingHom_forget (n : ℕ) :
    (perfectSupportedKMap Z.ι n).comp (qcqsConnectingHom j T Z hT hZ hcover n) =
      (PerfectMayerVietoris.qcqsConnectingHom j T hT hcover n).comp
        (perfectSupportedKMap ((j ⁻¹ᵁ T).ι ⁻¹ᵁ (j ⁻¹ᵁ Z)).ι (n+1)) := by
  let : QuasiSeparatedSpace V := QuasiSeparatedSpace.of_isOpenEmbedding j.isOpenEmbedding
  let : CompactSpace T.toScheme := isCompact_iff_compactSpace.mp hT
  let : CompactSpace (j ⁻¹ᵁ T).toScheme := isCompact_iff_compactSpace.mp (j.isCompact_preimage hT)
  exact connectingHom_forget j T Z hcover hZ n

end Quillen.PerfectComplexes.SupportedMayerVietoris
