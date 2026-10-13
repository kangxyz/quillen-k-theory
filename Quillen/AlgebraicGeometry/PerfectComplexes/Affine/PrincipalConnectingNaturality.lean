/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ConnectingNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.PairRestriction
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PrincipalPerfectLocalization

/-! # Original principal localization boundaries under geometric pair pullback -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes.Affine

/-- The actual principal open immersion, regarded as a qc ambient open pair. -/
abbrev principalOpenPair (R : CommRingCat.{u}) (r : R) : Quillen.Scheme.QuasiCompactOpenPairs.{u} :=
  ⟨⟨Arrow.mk (CoherentScheme.principalOpen R r),
    show IsOpenImmersion (CoherentScheme.principalOpen R r) from inferInstance⟩,
    show CompactSpace (Spec R) from inferInstance⟩

instance principalOpenPair_compactLeft (R : CommRingCat.{u}) (r : R) :
    CompactSpace (principalOpenPair R r).obj.obj.left :=
  inferInstanceAs (CompactSpace (Spec (.of (Localization.Away r))))

instance principalOpenPair_compactRight (R : CommRingCat.{u}) (r : R) :
    CompactSpace (principalOpenPair R r).obj.obj.right :=
  inferInstanceAs (CompactSpace (Spec R))

variable {R S : CommRingCat.{u}} {r : R} {s : S}

/-- Every original commuting principal-open square preserves the original
localization boundary, including the boundary from K₁ into supported K₀. -/
theorem principalPerfectConnectingHom_pullback
    (f : principalOpenPair R r ⟶ principalOpenPair S s) (n : ℕ) :
    (perfectSupportedKPullback f n).comp (principalPerfectConnectingHom S s n) =
    (principalPerfectConnectingHom R r n).comp (perfectKPullback f.hom.hom.left (n+1)) := by
  ext x
  obtain ⟨y, rfl⟩ := (principal_perfectOpenKRestrict_succ_bijective S s n).surjective x
  have hB := DFunLike.congr_fun (principalPerfectConnectingHom_comp_relative S s n) y
  have hF := DFunLike.congr_fun (perfectOpenConnectingHom_pullback f n) y
  have hO := DFunLike.congr_fun (perfectOpenKRestrict_pullback f (n+1)) y
  have hA := DFunLike.congr_fun (principalPerfectConnectingHom_comp_relative R r n)
    (perfectOpenKPullback f (n+1) y)
  exact (congrArg (perfectSupportedKPullback f n) hB).trans
    (hF.trans (hA.symm.trans (congrArg (principalPerfectConnectingHom R r n) hO.symm)))

/-- All original maps in principal connective localization commute with the
same arbitrary principal-open pair pullback. -/
theorem principalPerfect_longExactSequence_pullback
    (f : principalOpenPair R r ⟶ principalOpenPair S s) (n : ℕ) :
    (perfectSupportedKPullback f n).comp (principalPerfectConnectingHom S s n) =
      (principalPerfectConnectingHom R r n).comp (perfectKPullback f.hom.hom.left (n+1)) ∧
    (perfectKPullback f.hom.hom.right n).comp (perfectSupportedKMap (CoherentScheme.principalOpen S
      s) n) =
      (perfectSupportedKMap (CoherentScheme.principalOpen R r) n).comp (perfectSupportedKPullback f
        n) ∧
    (perfectKPullback f.hom.hom.left n).comp (perfectKRestrict (CoherentScheme.principalOpen S s) n)
      =
      (perfectKRestrict (CoherentScheme.principalOpen R r) n).comp (perfectKPullback f.hom.hom.right
        n) :=
  ⟨principalPerfectConnectingHom_pullback f n, perfectSupportedKMap_pullback f n,
    perfectKRestrict_pairPullback f n⟩

end Quillen.PerfectComplexes.Affine
