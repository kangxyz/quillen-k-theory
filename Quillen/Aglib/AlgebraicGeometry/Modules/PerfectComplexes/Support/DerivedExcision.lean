/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Support.ExtensionByZero
public import Quillen.Aglib.AlgebraicGeometry.Modules.DerivedCategory.ExtensionByZero
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.RestrictionHom
/-!
# Original derived Hom excision for a supported source

The actual localized extension-by-zero counit is invertible on a supported
perfect source for a covering pair. Its genuine derived adjunction gives
an equivalence whose forward map is exactly the original normalized
restriction on Hom. The inverse retains the original derived extension
and counit, and respects arbitrary derived target maps. The target is an
unrestricted all-sheaf complex: no perfectness, QC, or bound is assumed.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
attribute [local instance] Scheme.Modules.standardHasDerivedCategory
namespace Quillen.PerfectComplexes
attribute [local instance] HasDerivedCategory.standard
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)
  (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ T)
  {K : CochainComplex X.Modules ℤ} (hK : perfectSupported T.ι K) (L : CochainComplex X.Modules ℤ)

/-- The original localized counit is an isomorphism on the supported source. -/
def perfectSupportedDerivedCounitIso :
    (DerivedCategory.Q (C := X.Modules)).obj ((extensionByZero j).obj ((restrict j).obj K)) ≅
      (DerivedCategory.Q (C := X.Modules)).obj K := by
  have : QuasiIso ((extensionByZeroAdjunction j).counit.app K) :=
    extensionByZero_supported_counit_quasiIso j T hcover hK
  exact asIso ((DerivedCategory.Q (C := X.Modules)).map
    ((extensionByZeroAdjunction j).counit.app K))

@[simp] lemma perfectSupportedDerivedCounitIso_hom :
    (perfectSupportedDerivedCounitIso j T hcover hK).hom =
      (DerivedCategory.Q (C := X.Modules)).map ((extensionByZeroAdjunction j).counit.app K) := rfl

/-- Only the source needs support; the original all-sheaf target is arbitrary. -/
def perfectSupportedDerivedHomEquiv :
    ((DerivedCategory.Q (C := X.Modules)).obj K ⟶ (DerivedCategory.Q (C := X.Modules)).obj L) ≃
      ((DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj K) ⟶
        (DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj L)) :=
  ((perfectSupportedDerivedCounitIso j T hcover hK).symm.homCongr (Iso.refl _)).trans
    (extensionByZeroDerivedHomEquiv j ((restrict j).obj K) L)

/-- The forward map is precisely the original endpoint-normalized restriction. -/
@[simp] lemma perfectSupportedDerivedHomEquiv_apply
    (f : (DerivedCategory.Q (C := X.Modules)).obj K ⟶ (DerivedCategory.Q (C := X.Modules)).obj L) :
    perfectSupportedDerivedHomEquiv j T hcover hK L f = restrictDerivedHom j f := by
  change extensionByZeroDerivedHomEquiv j ((restrict j).obj K) L
    ((DerivedCategory.Q (C := X.Modules)).map ((extensionByZeroAdjunction j).counit.app K) ≫ f
      ≫ 𝟙 _) = _
  rw [Category.comp_id, extensionByZeroDerivedHomEquiv_postcomp,
    extensionByZeroDerivedHomEquiv_map, Adjunction.homEquiv_unit,
    (extensionByZeroAdjunction j).right_triangle_components, CategoryTheory.Functor.map_id,
      Category.id_comp]

/-- The inverse retains the original derived j! and the original counit. -/
lemma perfectSupportedDerivedHomEquiv_symm_apply
    (f : (DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj K) ⟶
      (DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj L)) :
    (perfectSupportedDerivedHomEquiv j T hcover hK L).symm f =
      (perfectSupportedDerivedCounitIso j T hcover hK).inv ≫
        extensionByZeroDerivedHom j f ≫
          (DerivedCategory.Q (C := X.Modules)).map
            ((extensionByZeroAdjunction j).counit.app L) := by
  change (perfectSupportedDerivedCounitIso j T hcover hK).inv ≫
    (extensionByZeroDerivedHomEquiv j ((restrict j).obj K) L).symm f ≫ 𝟙 _ = _
  rw [Category.comp_id, extensionByZeroDerivedHomEquiv_symm_eq]

@[simp] lemma restrictDerivedHom_perfectSupportedDerivedHomEquiv_symm
    (f : (DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj K) ⟶
      (DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj L)) :
    restrictDerivedHom j ((perfectSupportedDerivedHomEquiv j T hcover hK L).symm f) = f := by
  simpa only [perfectSupportedDerivedHomEquiv_apply] using
    (perfectSupportedDerivedHomEquiv j T hcover hK L).apply_symm_apply f

/-- The actual inverse respects arbitrary original derived target maps. -/
lemma perfectSupportedDerivedHomEquiv_symm_postcomp {L' : CochainComplex X.Modules ℤ}
    (f : (DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj K) ⟶
      (DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj L))
    (b : (DerivedCategory.Q (C := X.Modules)).obj L ⟶ (DerivedCategory.Q (C := X.Modules)).obj L') :
    (perfectSupportedDerivedHomEquiv j T hcover hK L).symm f ≫ b =
      (perfectSupportedDerivedHomEquiv j T hcover hK L').symm (f ≫ restrictDerivedHom j b) := by
  apply (perfectSupportedDerivedHomEquiv j T hcover hK L').injective
  simp only [perfectSupportedDerivedHomEquiv_apply, restrictDerivedHom_comp,
    restrictDerivedHom_perfectSupportedDerivedHomEquiv_symm]

include hcover hK in
/-- Original derived restriction is fully faithful on every supported source,
without any perfectness, quasicoherence, or boundedness condition on the target. -/
lemma restrictDerivedHom_bijective_of_supported_cover :
    Function.Bijective (restrictDerivedHom j (K := K) (L := L)) := by
  have he : ⇑(perfectSupportedDerivedHomEquiv j T hcover hK L) =
      restrictDerivedHom j := funext (perfectSupportedDerivedHomEquiv_apply j T hcover hK L)
  rw [← he]
  exact (perfectSupportedDerivedHomEquiv j T hcover hK L).bijective

end Quillen.PerfectComplexes
