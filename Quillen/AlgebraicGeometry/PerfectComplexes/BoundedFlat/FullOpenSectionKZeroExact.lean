/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionKZeroValue
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionRestrictionKComparison

/-!
# Degree-zero exactness of the original full-open section maps

The genuine coarse value map and the actual evaluation square identify the range of the
literal section restriction with the kernel of the original change-of-weak-equivalences map.
The quotient remains the original raw-perfect image quotient. Only the section evaluation
equivalences are used to choose witnesses; restriction is not assumed surjective on K-zero.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.AlgebraicGrothendieck
open AlgebraicGeometry.Scheme.AffineOpenPair
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R)
  [IsOpenImmersion j] [CompactSpace U]

/-- The literal section restriction image is the kernel of the unchanged section changeWeak. -/
theorem boundedFlatAffineFullOpenSection_changeWeakKMap_zero_range_ker (a : Under R) :
    (KMap (boundedFlatAffineFullOpenSectionRestriction_exact j a) 0).range =
      (KMap (Fibration.changeWeak_exact
        (boundedFlatAffineFullOpenSectionGrading j a).nested) 0).ker := by
  let P₀ := perfectOpenWeakWaldhausen (inclusion j a)
  let P := perfectWaldhausen (openSpace j a)
  let I := perfectRestrict (inclusion j a)
  let hI := perfectOpenRestrict_waldhausenExact (inclusion j a)
  let d := boundedFlatAffineFullOpenSectionGrading j a
  let r := KMap (boundedFlatAffineFullOpenSectionRestriction_exact j a) 0
  let g := KMap (Fibration.changeWeak_exact d.nested) 0
  let c := boundedFlatAffineFullOpenSectionKZeroValueMap j a
  let eP := grothendieckKZeroEquivOfSmallModel P
  let e₀ := grothendieckKZeroEquivOfSmallModel P₀
  let cV := boundedFlatAffineFullOpenSectionPerfectKEquiv j a 0
  let cW := boundedFlatAffineSectionOpenPerfectKEquiv (inclusion j a) 0
  let q := QuotientAddGroup.mk' (AlgebraicGrothendieck.map P₀ I hI).range
  have hq (x : (boundedFlatAffineFullOpenSectionWaldhausen j a).K 0) :
      c (g x) = q.toMultiplicative (eP.symm (cV x)) :=
    DFunLike.congr_fun (boundedFlatAffineFullOpenSectionKZeroValueMap_comp_changeWeak j a) x
  have hs (w : (boundedFlatAffineSectionOpenWaldhausen (inclusion j a)).K 0) :
      cV (r w) = KMap hI 0 (cW w) :=
    boundedFlatAffineFullOpenSectionRestriction_perfectKComparison j a 0 w
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    change g (r w) = 1
    apply boundedFlatAffineFullOpenSectionKZeroValueMap_injective j a
    have hz : q.toMultiplicative (eP.symm (cV (r w))) = 1 := by
      rw [hs, grothendieckKZeroEquivOfSmallModel_symm_natural P₀ P I hI]
      apply congrArg Multiplicative.ofAdd
      exact (QuotientAddGroup.eq_zero_iff _).mpr ⟨(e₀.symm (cW w)).toAdd, rfl⟩
    exact (hq (r w)).trans (hz.trans (map_one c).symm)
  · intro hx
    change g x = 1 at hx
    have hz : q (eP.symm (cV x)).toAdd = 0 := by
      have he := (hq x).symm.trans ((congrArg c hx).trans (map_one c))
      exact congrArg Multiplicative.toAdd he
    obtain ⟨z, hz⟩ := (QuotientAddGroup.eq_zero_iff _).mp hz
    obtain ⟨w, hw⟩ := cW.surjective (e₀ (Multiplicative.ofAdd z))
    refine ⟨w, ?_⟩
    change r w = x
    apply cV.injective
    apply eP.symm.injective
    rw [hs, grothendieckKZeroEquivOfSmallModel_symm_natural P₀ P I hI,
      hw, MulEquiv.symm_apply_apply]
    exact congrArg Multiplicative.ofAdd hz

end Quillen.PerfectComplexes
