/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeOpenNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasquePhiInverse

/-! # Original native Phi under scheme isomorphism and on all affine schemes

Actual inverse restriction maps and the original open-naturality square
transport bijectivity. Every affine scheme therefore reduces through its
original isoSpec to the accepted original affine projective-line map.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry
namespace Quillen.PerfectComplexes.ProjectiveLine
open Quillen.Scheme Quillen.Scheme.ProjectiveLine

/-- Original geometric restriction through a scheme isomorphism is an actual K-equivalence. -/
def perfectKRestrictIsoEquiv {U X : Scheme.{u}} (e : U ≅ X) (n : ℕ) :
    PerfectK X n ≃* PerfectK U n where
  toFun := perfectKRestrict e.hom n
  invFun := perfectKRestrict e.inv n
  left_inv x := by
    change ((perfectKRestrict e.inv n).comp (perfectKRestrict e.hom n)) x = x
    rw [← perfectKRestrict_comp]
    simp only [e.inv_hom_id, perfectKRestrict_id, MonoidHom.id_apply]
  right_inv x := by
    change ((perfectKRestrict e.hom n).comp (perfectKRestrict e.inv n)) x = x
    rw [← perfectKRestrict_comp]
    simp only [e.hom_inv_id, perfectKRestrict_id, MonoidHom.id_apply]
  map_mul' := (perfectKRestrict e.hom n).map_mul

/-- Original native Phi bijectivity transports through the actual geometric scheme isomorphism. -/
theorem nativeTwoSummandKMap_bijective_of_iso {U X : QuasiCompactSchemes.{u}}
    (e : U.obj ≅ X.obj) (n : ℕ) (hX : Function.Bijective (nativeTwoSummandKMap X n)) :
    Function.Bijective (nativeTwoSummandKMap U n) := by
  let eqc : U ≅ X := ObjectProperty.isoMk _ e
  let ep : (nativeLineFunctor.obj U).obj ≅ (nativeLineFunctor.obj X).obj :=
    quasiCompactSchemesInclusion.mapIso (nativeLineFunctor.mapIso eqc)
  let b := perfectKRestrictIsoEquiv e n
  let p := perfectKRestrictIsoEquiv ep n
  let bb := MulEquiv.prodCongr b b
  have h : nativeTwoSummandKMap U n =
      p.toMonoidHom.comp ((nativeTwoSummandKMap X n).comp bb.symm.toMonoidHom) := by
    ext a
    obtain ⟨a₁, a₂⟩ := a
    have hnat := nativeTwoSummandKMap_open eqc.hom n (b.symm a₁) (b.symm a₂)
    change perfectKRestrict ep.hom n
        (nativeTwoSummandKMap X n (b.symm a₁, b.symm a₂)) =
      nativeTwoSummandKMap U n (b (b.symm a₁), b (b.symm a₂)) at hnat
    change nativeTwoSummandKMap U n (a₁, a₂) =
      perfectKRestrict ep.hom n (nativeTwoSummandKMap X n (b.symm a₁, b.symm a₂))
    simpa only [MulEquiv.apply_symm_apply] using hnat.symm
  rw [h]
  exact p.bijective.comp (hX.comp bb.symm.bijective)

/-- Scheme-isomorphic native bases have equivalent original Phi-bijectivity assertions. -/
theorem nativeTwoSummandKMap_bijective_iff_of_iso {U X : QuasiCompactSchemes.{u}}
    (e : U.obj ≅ X.obj) (n : ℕ) :
    Function.Bijective (nativeTwoSummandKMap U n) ↔
      Function.Bijective (nativeTwoSummandKMap X n) :=
  ⟨nativeTwoSummandKMap_bijective_of_iso e.symm n,
    nativeTwoSummandKMap_bijective_of_iso e n⟩

/-- Every actual affine scheme has bijective original native Phi, including degree zero. -/
theorem nativeTwoSummandKMap_bijective_of_isAffine (X : QuasiCompactSchemes.{u})
    [IsAffine X.obj] (n : ℕ) : Function.Bijective (nativeTwoSummandKMap X n) :=
  nativeTwoSummandKMap_bijective_of_iso X.obj.isoSpec n
    (FlasquePhiInverse.nativeTwoSummandKMap_affine_bijective _ n)

end Quillen.PerfectComplexes.ProjectiveLine
