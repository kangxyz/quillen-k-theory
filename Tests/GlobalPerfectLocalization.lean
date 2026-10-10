/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.GlobalLocalizationNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.QuasiCompactPerfectLocalization

/-!
# Original-map consumers of global qcqs perfect localization

The tests retain unique original positive lifts, the precise K-zero image and
quotient comparison, the honest exact K-zero tail, agreement with the earlier
affine boundary, empty-open inverse laws, and arbitrary original pair squares.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace Quillen.Tests.GlobalPerfectLocalization
open PerfectComplexes PerfectComplexes.OpenDerivedImage

/-- Every positive original target class has one and only one relative lift. -/
theorem original_positive_unique_preimage {U X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
    (j : U ⟶ X) [IsOpenImmersion j]
    (n : ℕ) (y : PerfectK U (n+1)) :
    ∃! x : PerfectOpenK j (n+1), perfectOpenKRestrict j (n+1) x = y := by
  have hb := qcqs_perfectOpenKRestrict_succ_bijective j n
  obtain ⟨x, hx⟩ := hb.surjective y
  exact ⟨x, hx, fun z hz => hb.injective (hz.trans hx.symm)⟩

/-- Degree-zero lifts are unique exactly on the original global restriction image. -/
theorem original_KZero_unique_iff {U X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
    (j : U ⟶ X) [IsOpenImmersion j]
    (y : PerfectK U 0) :
    (∃! x : PerfectOpenK j 0, perfectOpenKRestrict j 0 x = y) ↔
      y ∈ (perfectKRestrict j 0).range := by
  constructor
  · rintro ⟨x, rfl, _⟩
    rw [← range_perfectOpenKRestrict_zero j]
    exact ⟨x, rfl⟩
  · intro hy
    let y' : PerfectOpenKZeroImage j := ⟨y, hy⟩
    let x := (qcqsPerfectOpenKZeroImageEquiv j).symm y'
    have hx : perfectOpenKRestrict j 0 x = y :=
      congrArg Subtype.val ((qcqsPerfectOpenKZeroImageEquiv j).apply_symm_apply y')
    exact ⟨x, hx, fun z hz => qcqs_perfectOpenKRestrict_zero_injective j (hz.trans hx.symm)⟩

/-- The K-zero equivalence agrees with the unchanged quotient-image endpoint. -/
theorem original_KZero_quotient_comparison {U X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
    (j : U ⟶ X) [IsOpenImmersion j]
    (x : PerfectOpenK j 0) :
    qcqsPerfectOpenKZeroImageEquiv j x =
      perfectOpenKZeroQuotientImageEquiv j (QuotientGroup.mk x) := by
  apply Subtype.ext
  rfl

/-- All three actual exact tail positions hold, including support degree zero. -/
theorem original_zero_tail {U X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
    (j : U ⟶ X) [IsOpenImmersion j] :
    (perfectKRestrict j 1).range = (qcqsPerfectConnectingHom j 0).ker ∧
    (qcqsPerfectConnectingHom j 0).range = (perfectSupportedKMap j 0).ker ∧
    (perfectSupportedKMap j 0).range = (perfectKRestrict j 0).ker :=
  qcqsPerfect_zeroTail j

/-- The global endpoint specializes to the accepted affine boundary literally,
so changing the proven roof source does not change the public map. -/
theorem original_affine_boundary_agreement (R : CommRingCat.{u}) (W : (Spec R).Opens)
    (hW : IsCompact (W : Set (Spec R))) (n : ℕ) :
    let : CompactSpace W.toScheme := isCompact_iff_compactSpace.mp hW
    qcqsPerfectConnectingHom W.ι n =
      Affine.quasiCompactPerfectConnectingHom R W hW n := by
  let : CompactSpace W.toScheme := isCompact_iff_compactSpace.mp hW
  dsimp only
  symm
  exact qcqsPerfectConnectingHom_unique W.ι n _
    (Affine.quasiCompactPerfectConnectingHom_comp_relative R W hW n)

/-- Empty opens instantiate the full genuine geometric endpoint without a
nonempty-source premise or a supplied roof. -/
theorem empty_open_original_inverse (R : CommRingCat.{u}) (n : ℕ)
    (x : PerfectOpenK (⊥ : (Spec R).Opens).ι (n+1)) :
    let : CompactSpace (⊥ : (Spec R).Opens).toScheme :=
      isCompact_iff_compactSpace.mp isCompact_empty
    (qcqsPerfectOpenKEquiv (⊥ : (Spec R).Opens).ι
      n).symm
      (perfectOpenKRestrict (⊥ : (Spec R).Opens).ι (n+1) x) = x := by
  let : CompactSpace (⊥ : (Spec R).Opens).toScheme :=
    isCompact_iff_compactSpace.mp isCompact_empty
  exact (qcqsPerfectOpenKEquiv (⊥ : (Spec R).Opens).ι
    n).symm_apply_apply x

/-- Naturality retains both original supported and ordinary perfect pullbacks. -/
theorem original_boundary_pair_square
    {A B : Quillen.Scheme.QuasiCompactOpenPairs.{u}}
    [QuasiSeparatedSpace A.obj.obj.right] [QuasiSeparatedSpace B.obj.obj.right]
    [CompactSpace A.obj.obj.left] [CompactSpace B.obj.obj.left]
    (f : A ⟶ B) (n : ℕ) (x : PerfectK B.obj.obj.left (n+1)) :
    perfectSupportedKPullback f n (qcqsPerfectConnectingHom B.obj.obj.hom n x) =
      qcqsPerfectConnectingHom A.obj.obj.hom n (perfectKPullback f.hom.hom.left (n+1) x) :=
  DFunLike.congr_fun (qcqsPerfectConnectingHom_pullback f n) x

end Quillen.Tests.GlobalPerfectLocalization
