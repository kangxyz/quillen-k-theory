/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.NativeOpenNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.RestrictionIsoEquivalence
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
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.ProjectiveLine

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
