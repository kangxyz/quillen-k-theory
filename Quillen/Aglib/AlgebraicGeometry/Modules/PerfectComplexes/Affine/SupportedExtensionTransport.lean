/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Support.RestrictionVanishing
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Affine.SupportedStabilizedExtension
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Affine.StabilizedExtensionTransport
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.Complex.Restriction
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Restriction
/-!
# Supported stabilization for original affine open immersions

A perfect complex on a compact open immersion into an affine scheme, vanishing
on the inverse image of a compact open Z, extends after the literal positive
stabilization E plus E[1] to an actual strict-perfect complex vanishing on Z.
The proof transports the genuine supported Spec theorem through the original
image isomorphism and isoSpec, preserving original restrictions and support.
The target E is an arbitrary all-sheaf complex satisfying local perfectness.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
attribute [local instance] Affine.standardDerivedModules Affine.standardDerivedSheaves
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Supported stabilization for an arbitrary original compact open immersion
into Spec R, with its original source and the actual inverse-image support. -/
lemma exists_strict_supported_stabilized_extension_into_spec (R : CommRingCat.{u})
    {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j] [CompactSpace U]
    (Z : (Spec R).Opens) (hZ : IsCompact (Z : Set (Spec R)))
    (E : CochainComplex U.Modules ℤ) (hE : locallyPerfect U E)
    (hz : IsZero ((DerivedCategory.Q (C := (j ⁻¹ᵁ Z).toScheme.Modules)).obj
      ((restrict (j ⁻¹ᵁ Z).ι).obj E))) :
    ∃ Q : CochainComplex (Spec R).Modules ℤ, strictPerfect (Spec R) Q ∧
      Nonempty ((DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj Q) ≅
        (DerivedCategory.Q (C := U.Modules)).obj (E ⊞ E⟦(1 : ℤ)⟧)) ∧
      IsZero ((DerivedCategory.Q (C := Z.toScheme.Modules)).obj ((restrict Z.ι).obj Q)) := by
  let W := j.opensRange
  have hW : IsCompact (W : Set (Spec R)) := isCompact_range j.continuous
  let E' := (restrict j.isoOpensRange.inv).obj E
  have hE' := locallyPerfect_restrict j.isoOpensRange.inv hE
  have hzero : IsZero ((DerivedCategory.Q (C := (W ⊓ Z).toScheme.Modules)).obj
      ((restrict ((Spec R).homOfLE (inf_le_left : W ⊓ Z ≤ W))).obj E')) := by
    have h := (isZero_restrict_image_source_iff j (j ⁻¹ᵁ Z) E).mpr hz
    have hi : supportImageOpen j (j ⁻¹ᵁ Z) = W ⊓ Z := by
      rw [supportImageOpen_eq_image, Scheme.Hom.image_preimage_eq_opensRange_inf]
    have hh (A : (Spec R).Opens) (hA : A ≤ W) (ha : supportImageOpen j (j ⁻¹ᵁ Z) = A) :
        IsZero ((DerivedCategory.Q (C := A.toScheme.Modules)).obj
          ((restrict ((Spec R).homOfLE hA)).obj E')) := by
      subst A
      exact h
    exact hh _ _ hi
  obtain ⟨P, hP, ⟨eQ⟩, hPZ⟩ :=
    Affine.locallyPerfect_exists_stabilized_extension_with_open_support R W Z hW hZ E' hE' hzero
  let Q := (Affine.associatedComplex R).obj P
  let eleft : (restrict j).obj Q ≅
      (restrict j.isoOpensRange.hom).obj ((restrict W.ι).obj Q) :=
    ((restrictCompIso j.isoOpensRange.hom W.ι ≪≫
      eqToIso (restrict_congr j.isoOpensRange_hom_ι)).symm).app Q
  let eE : (restrict j.isoOpensRange.hom).obj E' ≅ E :=
    (restrictCompIso j.isoOpensRange.hom j.isoOpensRange.inv ≪≫
      eqToIso (restrict_congr j.isoOpensRange.hom_inv_id) ≪≫ restrictIdIso U).app E
  let eright := restrictStabilizationIso j.isoOpensRange.hom E' ≪≫
    biprod.mapIso eE ((shiftFunctor (CochainComplex U.Modules ℤ) (1 : ℤ)).mapIso eE)
  exact ⟨Q, Affine.strictPerfect_associated R hP, ⟨(DerivedCategory.Q
    (C := U.Modules)).mapIso eleft ≪≫
    restrictDerivedIso j.isoOpensRange.hom eQ ≪≫ (DerivedCategory.Q
      (C := U.Modules)).mapIso eright⟩, hPZ⟩

/-- Supported stabilization along an arbitrary compact open immersion into
an affine scheme, retaining the original global support open. -/
lemma exists_strict_supported_stabilized_extension_into_affine {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [IsAffine X] [CompactSpace U]
    (Z : X.Opens) (hZ : IsCompact (Z : Set X))
    (E : CochainComplex U.Modules ℤ) (hE : locallyPerfect U E)
    (hz : IsZero ((DerivedCategory.Q (C := (j ⁻¹ᵁ Z).toScheme.Modules)).obj
      ((restrict (j ⁻¹ᵁ Z).ι).obj E))) :
    ∃ Q : CochainComplex X.Modules ℤ, strictPerfect X Q ∧
      Nonempty ((DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj Q) ≅
        (DerivedCategory.Q (C := U.Modules)).obj (E ⊞ E⟦(1 : ℤ)⟧)) ∧
      IsZero ((DerivedCategory.Q (C := Z.toScheme.Modules)).obj ((restrict Z.ι).obj Q)) := by
  let T := supportImageOpen X.isoSpec.hom Z
  have hT := isCompact_supportImageOpen X.isoSpec.hom Z hZ
  have hz' : IsZero ((DerivedCategory.Q (C := ((j ≫ X.isoSpec.hom) ⁻¹ᵁ T).toScheme.Modules)).obj
      ((restrict ((j ≫ X.isoSpec.hom) ⁻¹ᵁ T).ι).obj E)) := by
    have he : (j ≫ X.isoSpec.hom) ⁻¹ᵁ T = j ⁻¹ᵁ Z := by
      dsimp only [T]
      rw [Scheme.Hom.comp_preimage, supportImageOpen_eq_image, Scheme.Hom.preimage_image_eq]
    rw [he]
    exact hz
  obtain ⟨Q, hQ, ⟨eQ⟩, hQZ⟩ := exists_strict_supported_stabilized_extension_into_spec _
    (j ≫ X.isoSpec.hom) T hT E hE hz'
  exact ⟨(restrict X.isoSpec.hom).obj Q, strictPerfect_restrict X.isoSpec.hom hQ,
    ⟨(DerivedCategory.Q (C := U.Modules)).mapIso ((restrictCompIso j X.isoSpec.hom).app Q) ≪≫ eQ⟩,
    (isZero_restrict_supportImage_iff X.isoSpec.hom Z Q).mp hQZ⟩
end Quillen.PerfectComplexes
