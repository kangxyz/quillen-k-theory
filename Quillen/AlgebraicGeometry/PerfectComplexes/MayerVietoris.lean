/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.Excision
public import Quillen.Algebra.Group.MayerVietoris
public import Quillen.AlgebraicGeometry.PerfectComplexes.GlobalLocalizationNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.RestrictionComparison
public import Quillen.Waldhausen.Additivity.GroupFormula
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.KZeroCover

/-! # Original two-open connective Mayer–Vietoris maps and exact positions

The genuine original support-excision and localization ladders give the positive
exact positions. Original dense-image obstruction naturality and actual derived
isomorphism gluing also prove the final local-pair degree-zero position.
No surjectivity onto the overlap K-zero group or space-level fiber equivalence
is asserted.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace Quillen.PerfectComplexes.PerfectMayerVietoris
variable {V X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace V]
  [QuasiSeparatedSpace V]
  (j : V ⟶ X) [IsOpenImmersion j] (T : X.Opens) [CompactSpace T.toScheme] [CompactSpace (j ⁻¹ᵁ
    T).toScheme]
  (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ T)

/-- The commutative structure on original perfect K-groups supplied by additivity. -/
local instance (Y : Scheme.{u}) (n : ℕ) : CommGroup (PerfectK Y n) :=
  Waldhausen.Additivity.KCommGroup (perfectWaldhausen Y) n

/-- The original restriction pair, with the T factor first. -/
def restrictionPair (n : ℕ) : PerfectK X n →* PerfectK T.toScheme n × PerfectK V n :=
  GroupMayerVietoris.pair (perfectKRestrict T.ι n) (perfectKRestrict j n)

/-- The original overlap difference is the T-restriction times the inverse
of the V-restriction. This fixes the Mayer–Vietoris sign convention. -/
def overlapDifference (n : ℕ) : PerfectK T.toScheme n × PerfectK V n →*
    PerfectK (j ⁻¹ᵁ T).toScheme n :=
  GroupMayerVietoris.difference
    (perfectKRestrict (j.resLE T (j ⁻¹ᵁ T) le_rfl) n)
    (perfectKRestrict (j ⁻¹ᵁ T).ι n)

/-- The lower original localization boundary, transported through actual
support excision and retaining the existing supported group on X. -/
def lowerBoundary (n : ℕ) : PerfectK (j ⁻¹ᵁ T).toScheme (n+1) →* PerfectSupportedK T.ι n :=
  (perfectSupportedExcisionKEquiv j T hcover n).symm.toMonoidHom.comp
    (qcqsPerfectConnectingHom (j ⁻¹ᵁ T).ι n)

/-- The genuine original boundary into K(X), with no new choice of endpoint map. -/
def connectingHom (n : ℕ) : PerfectK (j ⁻¹ᵁ T).toScheme (n+1) →* PerfectK X n :=
  (perfectSupportedKMap T.ι n).comp (lowerBoundary j T hcover n)

omit [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace V]
  [QuasiSeparatedSpace V] [CompactSpace T.toScheme] [CompactSpace (j ⁻¹ᵁ T).toScheme] in
/-- The actual two restriction routes agree by the original resLE square. -/
lemma restriction_square (n : ℕ) :
    (perfectKRestrict (j.resLE T (j ⁻¹ᵁ T) le_rfl) n).comp (perfectKRestrict T.ι n) =
      (perfectKRestrict (j ⁻¹ᵁ T).ι n).comp (perfectKRestrict j n) := by
  rw [← perfectKRestrict_comp, ← perfectKRestrict_comp]
  congr 1
  exact j.resLE_comp_ι le_rfl

/-- The normalized lower boundary is compatible with the entire original
upper localization boundary, including the boundary into supported K-zero. -/
lemma lowerBoundary_comp_overlap (n : ℕ) :
    (lowerBoundary j T hcover n).comp
        (perfectKRestrict (j.resLE T (j ⁻¹ᵁ T) le_rfl) (n+1)) =
      qcqsPerfectConnectingHom T.ι n := by
  have h := @qcqsPerfectConnectingHom_pullback _ _
    (inferInstanceAs (QuasiSeparatedSpace V)) (inferInstanceAs (QuasiSeparatedSpace X))
    (inferInstanceAs (CompactSpace (j ⁻¹ᵁ T).toScheme))
    (inferInstanceAs (CompactSpace T.toScheme)) (qcSupportRestrictionPair j T) n
  change (perfectSupportedKPullback (qcSupportRestrictionPair j T) n).comp
      (qcqsPerfectConnectingHom T.ι n) =
    (qcqsPerfectConnectingHom (j ⁻¹ᵁ T).ι n).comp
      (perfectKPullback (j.resLE T (j ⁻¹ᵁ T) le_rfl) (n+1)) at h
  rw [← perfectSupportedKRestrict_eq_pullback, perfectKPullback_eq_restrict] at h
  ext x
  have hx : perfectSupportedKRestrict j T n (qcqsPerfectConnectingHom T.ι n x) =
      qcqsPerfectConnectingHom (j ⁻¹ᵁ T).ι n
        (perfectKRestrict (j.resLE T (j ⁻¹ᵁ T) le_rfl) (n+1) x) :=
    DFunLike.congr_fun h x
  apply (perfectSupportedExcisionKEquiv j T hcover n).injective
  change (perfectSupportedExcisionKEquiv j T hcover n)
    ((perfectSupportedExcisionKEquiv j T hcover n).symm
      (qcqsPerfectConnectingHom (j ⁻¹ᵁ T).ι n
        (perfectKRestrict (j.resLE T (j ⁻¹ᵁ T) le_rfl) (n+1) x))) =
    perfectSupportedKRestrict j T n (qcqsPerfectConnectingHom T.ι n x)
  rw [MulEquiv.apply_symm_apply]
  exact hx.symm

omit [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace T.toScheme] in
/-- Exactness of the transported lower boundary at the original support group. -/
lemma range_lowerBoundary (n : ℕ) :
    (lowerBoundary j T hcover n).range =
      ((perfectKRestrict j n).comp (perfectSupportedKMap T.ι n)).ker := by
  have hs := perfectSupportedKRestrict_comp_forget j T n
  have hs' (a : PerfectSupportedK T.ι n) :
      perfectSupportedKMap (j ⁻¹ᵁ T).ι n (perfectSupportedKRestrict j T n a) =
        perfectKRestrict j n (perfectSupportedKMap T.ι n a) := DFunLike.congr_fun hs a
  have he := range_qcqsPerfectConnectingHom_eq_ker_perfectSupportedKMap (j ⁻¹ᵁ T).ι n
  ext a
  constructor
  · rintro ⟨x,rfl⟩
    have hx : qcqsPerfectConnectingHom (j ⁻¹ᵁ T).ι n x ∈
        (perfectSupportedKMap (j ⁻¹ᵁ T).ι n).ker :=
      he ▸ (show qcqsPerfectConnectingHom (j ⁻¹ᵁ T).ι n x ∈
        (qcqsPerfectConnectingHom (j ⁻¹ᵁ T).ι n).range from ⟨x,rfl⟩)
    change perfectKRestrict j n (perfectSupportedKMap T.ι n _) = 1
    rw [← hs']
    change perfectSupportedKMap (j ⁻¹ᵁ T).ι n
      ((perfectSupportedExcisionKEquiv j T hcover n)
        ((perfectSupportedExcisionKEquiv j T hcover n).symm
          (qcqsPerfectConnectingHom (j ⁻¹ᵁ T).ι n x))) = 1
    rw [MulEquiv.apply_symm_apply]
    exact hx
  · intro ha
    have hm : perfectSupportedKRestrict j T n a ∈
        (qcqsPerfectConnectingHom (j ⁻¹ᵁ T).ι n).range := by
      rw [he]
      change perfectSupportedKMap (j ⁻¹ᵁ T).ι n (perfectSupportedKRestrict j T n a) = 1
      rw [hs']
      exact ha
    obtain ⟨x,hx⟩ := hm
    refine ⟨x,?_⟩
    change (perfectSupportedExcisionKEquiv j T hcover n).symm
      (qcqsPerfectConnectingHom (j ⁻¹ᵁ T).ι n x) = a
    rw [hx]
    exact (perfectSupportedExcisionKEquiv j T hcover n).symm_apply_apply a

omit [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace T.toScheme] in
include hcover in
/-- The common support image is the lower restriction kernel, because its
actual excision comparison is surjective even in degree zero. -/
lemma range_restrict_comp_support (n : ℕ) :
    ((perfectKRestrict j n).comp (perfectSupportedKMap T.ι n)).range =
      (perfectKRestrict (j ⁻¹ᵁ T).ι n).ker := by
  rw [← perfectSupportedKRestrict_comp_forget]
  rw [← range_perfectSupportedKMap_eq_ker_qcqs_perfectKRestrict (j ⁻¹ᵁ T).ι n]
  ext d
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨perfectSupportedKRestrict j T n a,rfl⟩
  · rintro ⟨a,rfl⟩
    obtain ⟨b,hb⟩ := (perfectSupportedKRestrict_bijective_of_cover j T hcover n).surjective a
    exact ⟨b,by simp only [MonoidHom.comp_apply,hb]⟩

/-- Exactness at original K(X) in every connective degree, including zero. -/
lemma range_connectingHom_eq_ker_restrictionPair (n : ℕ) :
    (connectingHom j T hcover n).range = (restrictionPair j T n).ker :=
  GroupMayerVietoris.range_boundary_eq_ker_pair _ _ _ _
    (range_perfectSupportedKMap_eq_ker_qcqs_perfectKRestrict T.ι n)
    (range_lowerBoundary j T hcover n)

/-- Exactness at the positive original overlap group. -/
lemma range_overlapDifference_eq_ker_connectingHom (n : ℕ) :
    (overlapDifference j T (n+1)).range = (connectingHom j T hcover n).ker :=
  GroupMayerVietoris.range_difference_eq_ker_boundary _ _ _ _ _
    (range_qcqsPerfectConnectingHom_eq_ker_perfectSupportedKMap T.ι n)
    (by
      ext x
      rw [range_qcqs_perfectKRestrict_eq_ker_qcqsPerfectConnectingHom (j ⁻¹ᵁ T).ι n]
      change qcqsPerfectConnectingHom (j ⁻¹ᵁ T).ι n x = 1 ↔
        (perfectSupportedExcisionKEquiv j T hcover n).symm
          (qcqsPerfectConnectingHom (j ⁻¹ᵁ T).ι n x) = 1
      exact ((perfectSupportedExcisionKEquiv j T hcover n).symm.map_eq_one_iff).symm)
    (lowerBoundary_comp_overlap j T hcover n)

include hcover in
/-- Exactness at the pair of positive original local groups. This theorem
requires n+1 and asserts no final-pair degree-zero gluing statement. -/
lemma range_restrictionPair_eq_ker_overlapDifference (n : ℕ) :
    (restrictionPair j T (n+1)).range = (overlapDifference j T (n+1)).ker :=
  GroupMayerVietoris.range_pair_eq_ker_difference _ _ _ _ _ _ _
    (range_perfectSupportedKMap_eq_ker_qcqs_perfectKRestrict T.ι (n+1))
    (range_restrict_comp_support j T hcover (n+1))
    (range_qcqs_perfectKRestrict_eq_ker_qcqsPerfectConnectingHom T.ι n)
    (by
      ext x
      rw [range_qcqs_perfectKRestrict_eq_ker_qcqsPerfectConnectingHom (j ⁻¹ᵁ T).ι n]
      change qcqsPerfectConnectingHom (j ⁻¹ᵁ T).ι n x = 1 ↔
        (perfectSupportedExcisionKEquiv j T hcover n).symm
          (qcqsPerfectConnectingHom (j ⁻¹ᵁ T).ι n x) = 1
      exact ((perfectSupportedExcisionKEquiv j T hcover n).symm.map_eq_one_iff).symm)
    (restriction_square j T (n+1)) (lowerBoundary_comp_overlap j T hcover n)

end Quillen.PerfectComplexes.PerfectMayerVietoris

namespace Quillen.PerfectComplexes.PerfectMayerVietoris
variable {V X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace V]
  (j : V ⟶ X) [IsOpenImmersion j] (T : X.Opens) (hT : IsCompact (T : Set X))
  (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ T)

/-- On a genuine compact two-open cover of a qcqs scheme, all overlap
compactness and separation inputs for the original boundary are discharged. -/
def qcqsConnectingHom (n : ℕ) :
    PerfectK (j ⁻¹ᵁ T).toScheme (n+1) →* PerfectK X n := by
  letI : QuasiSeparatedSpace V := QuasiSeparatedSpace.of_isOpenEmbedding j.isOpenEmbedding
  letI : CompactSpace T.toScheme := isCompact_iff_compactSpace.mp hT
  letI : CompactSpace (j ⁻¹ᵁ T).toScheme := isCompact_iff_compactSpace.mp (j.isCompact_preimage hT)
  exact connectingHom j T hcover n

/-- All positive exact positions, ending honestly at the actual degree-zero
global term when n=0. The final local-pair K-zero gluing assertion is proved separately below. -/
theorem qcqs_positiveExactSequence (n : ℕ) :
    (restrictionPair j T (n+1)).range = (overlapDifference j T (n+1)).ker ∧
    (overlapDifference j T (n+1)).range = (qcqsConnectingHom j T hT hcover n).ker ∧
    (qcqsConnectingHom j T hT hcover n).range = (restrictionPair j T n).ker := by
  let : QuasiSeparatedSpace V := QuasiSeparatedSpace.of_isOpenEmbedding j.isOpenEmbedding
  let : CompactSpace T.toScheme := isCompact_iff_compactSpace.mp hT
  let : CompactSpace (j ⁻¹ᵁ T).toScheme := isCompact_iff_compactSpace.mp (j.isCompact_preimage hT)
  exact ⟨range_restrictionPair_eq_ker_overlapDifference j T hcover n,
    range_overlapDifference_eq_ker_connectingHom j T hcover n,
    range_connectingHom_eq_ker_restrictionPair j T hcover n⟩

/-- The genuine K1(overlap) → K0(X) → K0(T)×K0(V) tail is exact at K0(X);
the incoming overlap map has precisely the positive difference image as kernel. -/
theorem qcqs_zeroTail :
    (overlapDifference j T 1).range = (qcqsConnectingHom j T hT hcover 0).ker ∧
    (qcqsConnectingHom j T hT hcover 0).range = (restrictionPair j T 0).ker :=
  (qcqs_positiveExactSequence j T hT hcover 0).2

end Quillen.PerfectComplexes.PerfectMayerVietoris

/-! # Genuine final local-pair K-zero exactness on a qcqs two-open cover -/
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace Quillen.PerfectComplexes.PerfectMayerVietoris
variable {V X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace V]
  (j : V ⟶ X) [IsOpenImmersion j] (T : X.Opens) (hT : IsCompact (T : Set X))
  (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ T)
/-- The commutative structure on original perfect K-groups supplied by additivity. -/
local instance (Y : Scheme.{u}) (n : ℕ) : CommGroup (PerfectK Y n) :=
  Waldhausen.Additivity.KCommGroup (perfectWaldhausen Y) n

include hT hcover in
/-- The missing degree-zero pair exactness follows from genuine derived
isomorphism gluing and naturality of the original dense-image obstruction.
All four maps remain the original restrictions with the actual difference sign. -/
theorem qcqs_range_restrictionPair_zero_eq_ker_overlapDifference :
    (restrictionPair j T 0).range = (overlapDifference j T 0).ker := by
  let : QuasiSeparatedSpace V := QuasiSeparatedSpace.of_isOpenEmbedding j.isOpenEmbedding
  let : CompactSpace T.toScheme := isCompact_iff_compactSpace.mp hT
  let : CompactSpace (j ⁻¹ᵁ T).toScheme := isCompact_iff_compactSpace.mp (j.isCompact_preimage hT)
  exact GroupMayerVietoris.range_pair_eq_ker_difference_of_image_reflection
    (perfectSupportedKMap T.ι 0) (perfectKRestrict T.ι 0) (perfectKRestrict j 0)
    (perfectKRestrict (j.resLE T (j ⁻¹ᵁ T) le_rfl) 0) (perfectKRestrict (j ⁻¹ᵁ T).ι 0)
    (range_perfectSupportedKMap_eq_ker_qcqs_perfectKRestrict T.ι 0)
    (range_restrict_comp_support j T hcover 0) (restriction_square j T 0)
    (fun x ↦ (OpenDerivedImage.restrict_mem_range_iff_of_cover j T hT hcover x).mp)

/-- The complete connective Mayer–Vietoris tail is exact at all three stated
positions. No surjectivity onto K-zero of the overlap is asserted. -/
theorem qcqs_completeZeroTail :
    (overlapDifference j T 1).range = (qcqsConnectingHom j T hT hcover 0).ker ∧
    (qcqsConnectingHom j T hT hcover 0).range = (restrictionPair j T 0).ker ∧
    (restrictionPair j T 0).range = (overlapDifference j T 0).ker :=
  ⟨(qcqs_zeroTail j T hT hcover).1, (qcqs_zeroTail j T hT hcover).2,
    qcqs_range_restrictionPair_zero_eq_ker_overlapDifference j T hT hcover⟩

include hT hcover in
/-- Matching original local K-zero classes have a genuine original global
class, without supposing either single-open K-zero restriction is surjective. -/
theorem qcqs_matching_zero_classes_glue (x : PerfectK T.toScheme 0) (y : PerfectK V 0)
    (hxy : perfectKRestrict (j.resLE T (j ⁻¹ᵁ T) le_rfl) 0 x =
      perfectKRestrict (j ⁻¹ᵁ T).ι 0 y) :
    ∃ z : PerfectK X 0, perfectKRestrict T.ι 0 z = x ∧ perfectKRestrict j 0 z = y := by
  have hx : (x,y) ∈ (overlapDifference j T 0).ker :=
    (GroupMayerVietoris.mem_difference_ker _ _ (x,y)).mpr hxy
  rw [← qcqs_range_restrictionPair_zero_eq_ker_overlapDifference j T hT hcover] at hx
  obtain ⟨z,hz⟩ := hx
  exact ⟨z,congrArg Prod.fst hz,congrArg Prod.snd hz⟩

end Quillen.PerfectComplexes.PerfectMayerVietoris
