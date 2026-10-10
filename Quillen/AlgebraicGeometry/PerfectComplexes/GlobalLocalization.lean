/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.GlobalCofinality

/-!
# Original qcqs connective perfect localization sequence

For any original compact open immersion into a qcqs scheme, the genuine
positive endpoint equivalence transports the original relative boundary to
perfect K-theory of the open. Its composite with perfectOpenKRestrict is the
literal original perfectOpenConnectingHom, and this equation determines it.

All three recurring exact positions retain the original restriction and
support-forgetting maps, including the actual K1(open) to K0(support) to
K0(base) to K0(open) tail. This is a connective endpoint with the honest
K-zero image; no additional surjectivity at its last arrow is assumed.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace Quillen.PerfectComplexes
open OpenDerivedImage
variable {U X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
  (j : U ⟶ X) [IsOpenImmersion j]

/-- Genuine supported boundary from original perfect K-theory of the compact open. -/
def qcqsPerfectConnectingHom (n : ℕ) :
    PerfectK U (n + 1) →*
      PerfectSupportedK j n :=
  (perfectOpenConnectingHom j n).comp
    (qcqsPerfectOpenKEquiv j n).symm.toMonoidHom

/-- The transported boundary retains the entire original relative boundary homomorphism. -/
theorem qcqsPerfectConnectingHom_comp_relative (n : ℕ) :
    (qcqsPerfectConnectingHom j n).comp
      (perfectOpenKRestrict j (n + 1)) =
    perfectOpenConnectingHom j n := by
  ext a
  change perfectOpenConnectingHom j n
    ((qcqsPerfectOpenKEquiv j n).symm ((qcqsPerfectOpenKEquiv j n) a)) = _
  rw [MulEquiv.symm_apply_apply]

/-- Exactness at original perfect K-theory on the qcqs base, including degree zero. -/
theorem range_perfectSupportedKMap_eq_ker_qcqs_perfectKRestrict (n : ℕ) :
    (perfectSupportedKMap j n).range =
      (perfectKRestrict j n).ker := by
  rw [range_perfectSupportedKMap_eq_ker_perfectOpenKMap]
  ext x
  change perfectOpenKMap j n x = 1 ↔
    perfectKRestrict j n x = 1
  have he := DFunLike.congr_fun
    (perfectOpenKRestrict_comp_perfectOpenKMap j n) x
  constructor
  · intro hx
    rw [← he, MonoidHom.comp_apply, hx, map_one]
  · intro hx
    apply qcqs_perfectOpenKRestrict_injective j n
    exact he.trans (hx.trans (map_one _).symm)

/-- The new boundary has exactly the original relative boundary image. -/
theorem range_qcqsPerfectConnectingHom (n : ℕ) :
    (qcqsPerfectConnectingHom j n).range =
      (perfectOpenConnectingHom j n).range := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨(qcqsPerfectOpenKEquiv j n).symm a, rfl⟩
  · rintro ⟨a, rfl⟩
    refine ⟨qcqsPerfectOpenKEquiv j n a, ?_⟩
    exact DFunLike.congr_fun (qcqsPerfectConnectingHom_comp_relative j n) a

/-- Exactness at original supported perfect K-theory, including its degree-zero group. -/
theorem range_qcqsPerfectConnectingHom_eq_ker_perfectSupportedKMap (n : ℕ) :
    (qcqsPerfectConnectingHom j n).range =
      (perfectSupportedKMap j n).ker := by
  rw [range_qcqsPerfectConnectingHom,
    range_perfectOpenConnectingHom_eq_ker_perfectSupportedKMap]

/-- Exactness at positive original perfect K-theory of the compact open. -/
theorem range_qcqs_perfectKRestrict_eq_ker_qcqsPerfectConnectingHom (n : ℕ) :
    (perfectKRestrict j (n + 1)).range =
      (qcqsPerfectConnectingHom j n).ker := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    change qcqsPerfectConnectingHom j n
      (perfectKRestrict j (n + 1) a) = 1
    rw [← DFunLike.congr_fun
      (perfectOpenKRestrict_comp_perfectOpenKMap j (n + 1)) a]
    change ((qcqsPerfectConnectingHom j n).comp
      (perfectOpenKRestrict j (n + 1)))
      (perfectOpenKMap j (n + 1) a) = 1
    rw [qcqsPerfectConnectingHom_comp_relative]
    have hm : perfectOpenKMap j (n + 1) a ∈
        (perfectOpenKMap j (n + 1)).range := ⟨a, rfl⟩
    rw [range_perfectOpenKMap_eq_ker_perfectOpenConnectingHom] at hm
    exact hm
  · intro hx
    have hm : (qcqsPerfectOpenKEquiv j n).symm x ∈
        (perfectOpenConnectingHom j n).ker := hx
    rw [← range_perfectOpenKMap_eq_ker_perfectOpenConnectingHom] at hm
    obtain ⟨a, ha⟩ := hm
    refine ⟨a, ?_⟩
    rw [← DFunLike.congr_fun
      (perfectOpenKRestrict_comp_perfectOpenKMap j (n + 1)) a]
    change qcqsPerfectOpenKEquiv j n
      (perfectOpenKMap j (n + 1) a) = x
    rw [ha, MulEquiv.apply_symm_apply]

/-- All recurring positions of the actual qcqs open connective localization sequence. -/
theorem qcqsPerfect_positiveLongExactSequence (n : ℕ) :
    (perfectKRestrict j (n + 1)).range =
      (qcqsPerfectConnectingHom j n).ker ∧
    (qcqsPerfectConnectingHom j n).range =
      (perfectSupportedKMap j n).ker ∧
    (perfectSupportedKMap j n).range =
      (perfectKRestrict j n).ker :=
  ⟨range_qcqs_perfectKRestrict_eq_ker_qcqsPerfectConnectingHom j n,
    range_qcqsPerfectConnectingHom_eq_ker_perfectSupportedKMap j n,
    range_perfectSupportedKMap_eq_ker_qcqs_perfectKRestrict j n⟩

/-- The actual K₁(open) → K₀(support) → K₀(base) → K₀(open) exact tail. -/
theorem qcqsPerfect_zeroTail :
    (perfectKRestrict j 1).range =
      (qcqsPerfectConnectingHom j 0).ker ∧
    (qcqsPerfectConnectingHom j 0).range =
      (perfectSupportedKMap j 0).ker ∧
    (perfectSupportedKMap j 0).range =
      (perfectKRestrict j 0).ker :=
  qcqsPerfect_positiveLongExactSequence j 0

/-- Compatibility with the unchanged relative boundary determines this endpoint uniquely. -/
theorem qcqsPerfectConnectingHom_unique (n : ℕ)
    (δ : PerfectK U (n + 1) →* PerfectSupportedK j n)
    (hδ : δ.comp (perfectOpenKRestrict j (n+1)) = perfectOpenConnectingHom j n) :
    δ = qcqsPerfectConnectingHom j n := by
  ext x
  obtain ⟨a, rfl⟩ := (qcqsPerfectOpenKEquiv j n).surjective x
  exact DFunLike.congr_fun (hδ.trans (qcqsPerfectConnectingHom_comp_relative j n).symm) a

end Quillen.PerfectComplexes
