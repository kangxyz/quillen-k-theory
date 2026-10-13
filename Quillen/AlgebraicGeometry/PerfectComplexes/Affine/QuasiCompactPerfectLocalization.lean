/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.QuasiCompactPerfectCofinality

/-! # Original quasi-compact affine-open connective localization sequence

The actual relative-open boundary is transported through the proved positive
quasi-compact affine-open endpoint equivalence. All original support-forgetting and restriction
maps remain unchanged. The degree-zero tail is exact without asserting
surjectivity onto K-zero of the open.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace Quillen.PerfectComplexes.Affine
variable (R : CommRingCat.{u}) (W : (Spec R).Opens)
  (hW : IsCompact (W : Set (Spec R)))

/-- Genuine supported boundary from original perfect K-theory of the quasi-compact affine open. -/
def quasiCompactPerfectConnectingHom (n : ℕ) :
    PerfectK W.toScheme (n + 1) →*
      PerfectSupportedK W.ι n :=
  (perfectOpenConnectingHom W.ι n).comp
    (quasiCompactPerfectOpenKEquiv R W hW n).symm.toMonoidHom

/-- The transported boundary retains the entire original relative boundary homomorphism. -/
theorem quasiCompactPerfectConnectingHom_comp_relative (n : ℕ) :
    (quasiCompactPerfectConnectingHom R W hW n).comp
      (perfectOpenKRestrict W.ι (n + 1)) =
    perfectOpenConnectingHom W.ι n := by
  ext a
  change perfectOpenConnectingHom W.ι n
    ((quasiCompactPerfectOpenKEquiv R W hW n).symm ((quasiCompactPerfectOpenKEquiv R W hW n) a)) = _
  rw [MulEquiv.symm_apply_apply]

include hW in
/-- Exactness at original perfect K-theory on the affine base, including degree zero. -/
theorem range_perfectSupportedKMap_eq_ker_quasiCompact_perfectKRestrict (n : ℕ) :
    (perfectSupportedKMap W.ι n).range =
      (perfectKRestrict W.ι n).ker := by
  rw [range_perfectSupportedKMap_eq_ker_perfectOpenKMap]
  ext x
  change perfectOpenKMap W.ι n x = 1 ↔
    perfectKRestrict W.ι n x = 1
  have he := DFunLike.congr_fun
    (perfectOpenKRestrict_comp_perfectOpenKMap W.ι n) x
  constructor
  · intro hx
    rw [← he, MonoidHom.comp_apply, hx, map_one]
  · intro hx
    apply quasiCompact_perfectOpenKRestrict_injective R W hW n
    exact he.trans (hx.trans (map_one _).symm)

/-- The new boundary has exactly the original relative boundary image. -/
theorem range_quasiCompactPerfectConnectingHom (n : ℕ) :
    (quasiCompactPerfectConnectingHom R W hW n).range =
      (perfectOpenConnectingHom W.ι n).range := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨(quasiCompactPerfectOpenKEquiv R W hW n).symm a, rfl⟩
  · rintro ⟨a, rfl⟩
    refine ⟨quasiCompactPerfectOpenKEquiv R W hW n a, ?_⟩
    exact DFunLike.congr_fun (quasiCompactPerfectConnectingHom_comp_relative R W hW n) a

/-- Exactness at original supported perfect K-theory, including its degree-zero group. -/
theorem range_quasiCompactPerfectConnectingHom_eq_ker_perfectSupportedKMap (n : ℕ) :
    (quasiCompactPerfectConnectingHom R W hW n).range =
      (perfectSupportedKMap W.ι n).ker := by
  rw [range_quasiCompactPerfectConnectingHom,
    range_perfectOpenConnectingHom_eq_ker_perfectSupportedKMap]

/-- Exactness at positive original perfect K-theory of the quasi-compact affine open. -/
theorem range_quasiCompact_perfectKRestrict_eq_ker_quasiCompactPerfectConnectingHom (n : ℕ) :
    (perfectKRestrict W.ι (n + 1)).range =
      (quasiCompactPerfectConnectingHom R W hW n).ker := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    change quasiCompactPerfectConnectingHom R W hW n
      (perfectKRestrict W.ι (n + 1) a) = 1
    rw [← DFunLike.congr_fun
      (perfectOpenKRestrict_comp_perfectOpenKMap W.ι (n + 1)) a]
    change ((quasiCompactPerfectConnectingHom R W hW n).comp
      (perfectOpenKRestrict W.ι (n + 1)))
      (perfectOpenKMap W.ι (n + 1) a) = 1
    rw [quasiCompactPerfectConnectingHom_comp_relative]
    have hm : perfectOpenKMap W.ι (n + 1) a ∈
        (perfectOpenKMap W.ι (n + 1)).range := ⟨a, rfl⟩
    rw [range_perfectOpenKMap_eq_ker_perfectOpenConnectingHom] at hm
    exact hm
  · intro hx
    have hm : (quasiCompactPerfectOpenKEquiv R W hW n).symm x ∈
        (perfectOpenConnectingHom W.ι n).ker := hx
    rw [← range_perfectOpenKMap_eq_ker_perfectOpenConnectingHom] at hm
    obtain ⟨a, ha⟩ := hm
    refine ⟨a, ?_⟩
    rw [← DFunLike.congr_fun
      (perfectOpenKRestrict_comp_perfectOpenKMap W.ι (n + 1)) a]
    change quasiCompactPerfectOpenKEquiv R W hW n
      (perfectOpenKMap W.ι (n + 1) a) = x
    rw [ha, MulEquiv.apply_symm_apply]

/-- All recurring positions of the actual quasi-compact affine-open connective localization
  sequence. -/
theorem quasiCompactPerfect_positiveLongExactSequence (n : ℕ) :
    (perfectKRestrict W.ι (n + 1)).range =
      (quasiCompactPerfectConnectingHom R W hW n).ker ∧
    (quasiCompactPerfectConnectingHom R W hW n).range =
      (perfectSupportedKMap W.ι n).ker ∧
    (perfectSupportedKMap W.ι n).range =
      (perfectKRestrict W.ι n).ker :=
  ⟨range_quasiCompact_perfectKRestrict_eq_ker_quasiCompactPerfectConnectingHom R W hW n,
    range_quasiCompactPerfectConnectingHom_eq_ker_perfectSupportedKMap R W hW n,
    range_perfectSupportedKMap_eq_ker_quasiCompact_perfectKRestrict R W hW n⟩

/-- The actual K₁(open) → K₀(support) → K₀(base) → K₀(open) exact tail. -/
theorem quasiCompactPerfect_zeroTail :
    (perfectKRestrict W.ι 1).range =
      (quasiCompactPerfectConnectingHom R W hW 0).ker ∧
    (quasiCompactPerfectConnectingHom R W hW 0).range =
      (perfectSupportedKMap W.ι 0).ker ∧
    (perfectSupportedKMap W.ι 0).range =
      (perfectKRestrict W.ι 0).ker :=
  quasiCompactPerfect_positiveLongExactSequence R W hW 0

/-- Compatibility with the unchanged relative boundary determines this endpoint uniquely. -/
theorem quasiCompactPerfectConnectingHom_unique (n : ℕ)
    (δ : PerfectK W.toScheme (n + 1) →* PerfectSupportedK W.ι n)
    (hδ : δ.comp (perfectOpenKRestrict W.ι (n + 1)) = perfectOpenConnectingHom W.ι n) :
    δ = quasiCompactPerfectConnectingHom R W hW n := by
  ext x
  obtain ⟨a, rfl⟩ := (quasiCompactPerfectOpenKEquiv R W hW n).surjective x
  exact DFunLike.congr_fun (hδ.trans (quasiCompactPerfectConnectingHom_comp_relative R W hW n).symm)
    a

end Quillen.PerfectComplexes.Affine
