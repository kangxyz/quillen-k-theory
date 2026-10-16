/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Affine.PrincipalDerivedImage


public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Affine.ModulePerfectClosure
public import Quillen.Aglib.AlgebraicGeometry.Modules.DerivedCategory.Affine.Comparison
public import Quillen.Waldhausen.Approximation.WeakImage
public import Aglib.Algebra.Homology.DerivedCategory.KProjective.Representatives

/-!
# The actual principal derived image and strict weak witnesses

The actual image of original bounded finite-projective module complexes under
principal localization is closed under shifts and distinguished extensions.
The key proof clears a genuine derived morphism's denominator, uses the
localized scalar automorphism, and takes the literal original global cone.

For explicitly termwise quasicoherent target complexes this derived image is
proved equivalent to existence of an actual strict restriction quasi-isomorphism,
using genuine K-projective representatives and original affine counits. Thus
the original strict witnessed image is weakly replete in both directions.
No extension of every localized strict object or removal of the K0 image
obstruction is asserted.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open HomologicalComplex
namespace Quillen.PerfectComplexes.Affine
open Quillen.ModuleComplex.PrincipalLocalization
attribute [local instance] HasDerivedCategory.standard Abelian.hasFiniteBiproducts

/-- The literal strict witnessed-image predicate has the proved module-derived
characterization; it is not a separately assumed derived-density condition. -/
lemma principal_strict_image_iff_moduleDerivedImage (R : CommRingCat.{u}) (r : R)
    (B : StrictPerfect (Spec (.of (Localization.Away r)))) :
    Waldhausen.ApproximationImage.objects (strictWaldhausen _)
      (strictRestrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)) B ↔
      principalModuleDerivedImage R r
        (DerivedCategory.Q.obj ((sectionsComplex (.of (Localization.Away r))).obj B.obj)) := by
  have hB (i : ℤ) : (B.obj.X i).IsQuasicoherent := by
    let := B.property.2 i
    infer_instance
  rw [← exists_principal_strict_quasiIso_iff_moduleDerivedImage R r B.obj hB]
  constructor
  · rintro ⟨E, q, hq⟩
    exact ⟨E, q.hom, hq⟩
  · rintro ⟨E, q, hq⟩
    exact ⟨E, ObjectProperty.homMk q, hq⟩

/-- Actual principal strict image membership is invariant in both directions
under an original quasi-isomorphism of strict targets. -/
lemma principal_strict_image_iff_of_weak (R : CommRingCat.{u}) (r : R)
    {A B : StrictPerfect (Spec (.of (Localization.Away r)))} (f : A ⟶ B)
    (hf : (strictWaldhausen _).weq f) :
    Waldhausen.ApproximationImage.objects (strictWaldhausen _)
      (strictRestrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)) A ↔
    Waldhausen.ApproximationImage.objects (strictWaldhausen _)
      (strictRestrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)) B := by
  rw [principal_strict_image_iff_moduleDerivedImage, principal_strict_image_iff_moduleDerivedImage]
  have hA (i : ℤ) : (A.obj.X i).IsQuasicoherent := by
    let := A.property.2 i
    infer_instance
  have hB (i : ℤ) : (B.obj.X i).IsQuasicoherent := by
    let := B.property.2 i
    infer_instance
  have : QuasiIso ((sectionsComplex (.of (Localization.Away r))).map f.hom) :=
    (quasiIso_sections_iff _ hA hB f.hom).mpr hf
  exact (principalModuleDerivedImage R r).prop_iff_of_iso
    (asIso (DerivedCategory.Q.map ((sectionsComplex (.of (Localization.Away r))).map f.hom)))


end Quillen.PerfectComplexes.Affine
