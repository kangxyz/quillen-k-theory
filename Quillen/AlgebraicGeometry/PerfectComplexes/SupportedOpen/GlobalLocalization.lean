/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.GlobalCofinality
public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.Forget
public import Quillen.AlgebraicGeometry.PerfectComplexes.GlobalLocalization

/-!
# Original qcqs supported connective localization

For qcqs X, compact original open U and compact auxiliary open T, the
positive supported equivalence transports the genuine relative boundary.
All three original range/kernel positions hold, including K1 to K0 and the
honest K0 tail. Source support is the complement of T; fiber support is the
complement of T union U; target support is the complement of j inverse-image T.
The original boundary and inverse endpoint commute with actual support
forgetting to the existing unsupplied-support perfect localization sequence.
No full-target K0 surjectivity is inferred.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace Quillen.PerfectComplexes
open SupportedOpenDerivedImage
variable {U X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
  (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens) (hT : IsCompact (T : Set X))
include hT

/-- Genuine supported boundary from original perfect K-theory of the compact open. -/
def qcqsPerfectSupportedConnectingHom (n : ℕ) :
    PerfectSupportedK (j ⁻¹ᵁ T).ι (n + 1) →*
      PerfectSupportedK (T ⊔ j.opensRange).ι n :=
  (perfectSupportedOpenConnectingHom j T n).comp
    (qcqsPerfectSupportedOpenKEquiv j T hT n).symm.toMonoidHom

/-- The transported boundary retains the entire original relative boundary homomorphism. -/
theorem qcqsPerfectSupportedConnectingHom_comp_relative (n : ℕ) :
    (qcqsPerfectSupportedConnectingHom j T hT n).comp
      (perfectSupportedOpenKRestrict j T (n + 1)) =
    perfectSupportedOpenConnectingHom j T n := by
  ext a
  change perfectSupportedOpenConnectingHom j T n
    ((qcqsPerfectSupportedOpenKEquiv j T hT n).symm ((qcqsPerfectSupportedOpenKEquiv j T hT n) a)) =
      _
  rw [MulEquiv.symm_apply_apply]

/-- Exactness at original perfect K-theory on the qcqs base, including degree zero. -/
theorem range_perfectSupportedUnionKMap_eq_ker_qcqs_perfectSupportedKRestrict (n : ℕ) :
    (perfectSupportedUnionKMap j T n).range =
      (perfectSupportedKRestrict j T n).ker := by
  rw [range_perfectSupportedUnionKMap_eq_ker_perfectSupportedOpenKMap]
  ext x
  change perfectSupportedOpenKMap j T n x = 1 ↔
    perfectSupportedKRestrict j T n x = 1
  have he := DFunLike.congr_fun
    (perfectSupportedOpenKRestrict_comp_perfectSupportedOpenKMap j T n) x
  constructor
  · intro hx
    rw [← he, MonoidHom.comp_apply, hx, map_one]
  · intro hx
    apply qcqs_perfectSupportedOpenKRestrict_injective j T hT n
    exact he.trans (hx.trans (map_one _).symm)

/-- The new boundary has exactly the original relative boundary image. -/
theorem range_qcqsPerfectSupportedConnectingHom (n : ℕ) :
    (qcqsPerfectSupportedConnectingHom j T hT n).range =
      (perfectSupportedOpenConnectingHom j T n).range := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨(qcqsPerfectSupportedOpenKEquiv j T hT n).symm a, rfl⟩
  · rintro ⟨a, rfl⟩
    refine ⟨qcqsPerfectSupportedOpenKEquiv j T hT n a, ?_⟩
    exact DFunLike.congr_fun (qcqsPerfectSupportedConnectingHom_comp_relative j T hT n) a

/-- Exactness at original supported perfect K-theory, including its degree-zero group. -/
theorem range_qcqsPerfectSupportedConnectingHom_eq_ker_perfectSupportedUnionKMap (n : ℕ) :
    (qcqsPerfectSupportedConnectingHom j T hT n).range =
      (perfectSupportedUnionKMap j T n).ker := by
  rw [range_qcqsPerfectSupportedConnectingHom,
    range_perfectSupportedOpenConnectingHom_eq_ker_perfectSupportedUnionKMap]

/-- Exactness at positive original perfect K-theory of the compact open. -/
theorem range_qcqs_perfectSupportedKRestrict_eq_ker_qcqsPerfectSupportedConnectingHom (n : ℕ) :
    (perfectSupportedKRestrict j T (n + 1)).range =
      (qcqsPerfectSupportedConnectingHom j T hT n).ker := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    change qcqsPerfectSupportedConnectingHom j T hT n
      (perfectSupportedKRestrict j T (n + 1) a) = 1
    rw [← DFunLike.congr_fun
      (perfectSupportedOpenKRestrict_comp_perfectSupportedOpenKMap j T (n + 1)) a]
    change ((qcqsPerfectSupportedConnectingHom j T hT n).comp
      (perfectSupportedOpenKRestrict j T (n + 1)))
      (perfectSupportedOpenKMap j T (n + 1) a) = 1
    rw [qcqsPerfectSupportedConnectingHom_comp_relative]
    have hm : perfectSupportedOpenKMap j T (n + 1) a ∈
        (perfectSupportedOpenKMap j T (n + 1)).range := ⟨a, rfl⟩
    rw [range_perfectSupportedOpenKMap_eq_ker_perfectSupportedOpenConnectingHom] at hm
    exact hm
  · intro hx
    have hm : (qcqsPerfectSupportedOpenKEquiv j T hT n).symm x ∈
        (perfectSupportedOpenConnectingHom j T n).ker := hx
    rw [← range_perfectSupportedOpenKMap_eq_ker_perfectSupportedOpenConnectingHom] at hm
    obtain ⟨a, ha⟩ := hm
    refine ⟨a, ?_⟩
    rw [← DFunLike.congr_fun
      (perfectSupportedOpenKRestrict_comp_perfectSupportedOpenKMap j T (n + 1)) a]
    change qcqsPerfectSupportedOpenKEquiv j T hT n
      (perfectSupportedOpenKMap j T (n + 1) a) = x
    rw [ha, MulEquiv.apply_symm_apply]

/-- All recurring positions of the actual qcqs open connective localization sequence. -/
theorem qcqsPerfectSupported_positiveLongExactSequence (n : ℕ) :
    (perfectSupportedKRestrict j T (n + 1)).range =
      (qcqsPerfectSupportedConnectingHom j T hT n).ker ∧
    (qcqsPerfectSupportedConnectingHom j T hT n).range =
      (perfectSupportedUnionKMap j T n).ker ∧
    (perfectSupportedUnionKMap j T n).range =
      (perfectSupportedKRestrict j T n).ker :=
  ⟨range_qcqs_perfectSupportedKRestrict_eq_ker_qcqsPerfectSupportedConnectingHom j T hT n,
    range_qcqsPerfectSupportedConnectingHom_eq_ker_perfectSupportedUnionKMap j T hT n,
    range_perfectSupportedUnionKMap_eq_ker_qcqs_perfectSupportedKRestrict j T hT n⟩

/-- The actual K₁(open) → K₀(support) → K₀(base) → K₀(open) exact tail. -/
theorem qcqsPerfectSupported_zeroTail :
    (perfectSupportedKRestrict j T 1).range =
      (qcqsPerfectSupportedConnectingHom j T hT 0).ker ∧
    (qcqsPerfectSupportedConnectingHom j T hT 0).range =
      (perfectSupportedUnionKMap j T 0).ker ∧
    (perfectSupportedUnionKMap j T 0).range =
      (perfectSupportedKRestrict j T 0).ker :=
  qcqsPerfectSupported_positiveLongExactSequence j T hT 0

/-- Compatibility with the unchanged relative boundary determines this endpoint uniquely. -/
theorem qcqsPerfectSupportedConnectingHom_unique (n : ℕ)
    (δ : PerfectSupportedK (j ⁻¹ᵁ T).ι (n + 1) →* PerfectSupportedK (T ⊔ j.opensRange).ι n)
    (hδ : δ.comp (perfectSupportedOpenKRestrict j T (n + 1)) = perfectSupportedOpenConnectingHom j T
      n) :
    δ = qcqsPerfectSupportedConnectingHom j T hT n := by
  ext x
  obtain ⟨a, rfl⟩ := (qcqsPerfectSupportedOpenKEquiv j T hT n).surjective x
  exact DFunLike.congr_fun (hδ.trans (qcqsPerfectSupportedConnectingHom_comp_relative j T hT
    n).symm) a

end Quillen.PerfectComplexes

end

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
  (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens) (hT : IsCompact (T : Set X))

/-- The actual supported boundary forgets to the existing original perfect boundary. -/
theorem qcqsPerfectSupportedConnectingHom_forget (n : ℕ) :
    (perfectSupportedUnionForgetKMap j T n).comp
        (qcqsPerfectSupportedConnectingHom j T hT n) =
      (qcqsPerfectConnectingHom j n).comp
        (perfectSupportedKMap (j ⁻¹ᵁ T).ι (n + 1)) := by
  ext x
  obtain ⟨a, rfl⟩ := (qcqs_perfectSupportedOpenKRestrict_succ_bijective j T hT n).surjective x
  have h₁ := DFunLike.congr_fun
    (qcqsPerfectSupportedConnectingHom_comp_relative j T hT n) a
  have h₂ := DFunLike.congr_fun
    (perfectSupportedOpenConnectingHom_forget j T n) a
  have h₃ := DFunLike.congr_fun
    (perfectSupportedOpenKForget_comp_restrict j T (n + 1)) a
  have h₄ := DFunLike.congr_fun
    (qcqsPerfectConnectingHom_comp_relative j n) (perfectSupportedOpenKForget j T (n + 1) a)
  simp only [MonoidHom.comp_apply] at h₁ h₂ h₃ h₄ ⊢
  rw [h₁, h₂, ← h₃, h₄]

/-- The positive inverse endpoint also respects the actual support-forgetting map. -/
theorem qcqsPerfectSupportedOpenKEquiv_symm_forget (n : ℕ)
    (x : PerfectSupportedK (j ⁻¹ᵁ T).ι (n + 1)) :
    perfectSupportedOpenKForget j T (n + 1) ((qcqsPerfectSupportedOpenKEquiv j T hT n).symm x) =
      (qcqsPerfectOpenKEquiv j n).symm (perfectSupportedKMap (j ⁻¹ᵁ T).ι (n + 1) x) := by
  apply (qcqsPerfectOpenKEquiv j n).injective
  change perfectOpenKRestrict j (n + 1)
    (perfectSupportedOpenKForget j T (n + 1) ((qcqsPerfectSupportedOpenKEquiv j T hT n).symm x)) = _
  have hs := DFunLike.congr_fun (perfectSupportedOpenKForget_comp_restrict j T (n + 1))
    ((qcqsPerfectSupportedOpenKEquiv j T hT n).symm x)
  simp only [MonoidHom.comp_apply] at hs
  rw [hs]
  change perfectSupportedKMap (j ⁻¹ᵁ T).ι (n + 1)
    (qcqsPerfectSupportedOpenKEquiv j T hT n ((qcqsPerfectSupportedOpenKEquiv j T hT n).symm x)) = _
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

end Quillen.PerfectComplexes

end
