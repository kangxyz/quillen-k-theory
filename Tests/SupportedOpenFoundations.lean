/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpenDerivedImage.Structure

/-! # Original-map consumers of supported restriction and image foundations -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace Quillen.Tests.SupportedOpenFoundations
open PerfectComplexes
attribute [local instance] HasDerivedCategory.standard Abelian.hasFiniteBiproducts

/-- The supported functor retains each original degreewise chain component. -/
theorem original_supported_restriction_components {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)
    {P Q : (perfectSupported T.ι).FullSubcategory} (f : P ⟶ Q) (n : ℤ) :
    (((perfectSupportedRestrict j T).map f).hom).f n =
      (Scheme.Modules.restrictFunctor j).map (f.hom.f n) := rfl

/-- The actual supported K-map commutes with the original public maps after
forgetting support, without a compactness or qcqs premise. -/
theorem original_supported_K_forget_square {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens) (n : ℕ)
    (x : PerfectSupportedK T.ι n) :
    perfectSupportedKMap (j ⁻¹ᵁ T).ι n (perfectSupportedKRestrict j T n x) =
      perfectKRestrict j n (perfectSupportedKMap T.ι n x) :=
  DFunLike.congr_fun (perfectSupportedKRestrict_comp_forget j T n) x

/-- The literal numerator cone has original restricted homology zero in every degree. -/
theorem original_supported_cone_homology {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] {P Q : Complex X}
    (hP : perfectSupported j P) (hQ : perfectSupported j Q) (f : P ⟶ Q) (n : ℤ) :
    IsZero (((restrict j).obj (CochainComplex.mappingCone f)).homology n) :=
  ((perfectSupported_mappingCone j hP hQ f).2 n).isZero_homology

/-- The actual global model and the actual complement both retain their
prescribed support and the original derived inverse equations. -/
theorem original_supported_complement {U X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
    (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens) (hT : IsCompact (T : Set X))
    (E : Complex U) (hE : perfectSupported (j ⁻¹ᵁ T).ι E) :
    ∃ (P : Complex X) (C : Complex U), perfectSupported T.ι P ∧
      perfectSupported (j ⁻¹ᵁ T).ι C ∧
      ∃ e : (toDerived U).obj ((restrict j).obj P) ≅ (toDerived U).obj (C ⊞ E),
        e.hom ≫ e.inv = 𝟙 _ ∧ e.inv ≫ e.hom = 𝟙 _ := by
  obtain ⟨C, hC, P, hP, ⟨e⟩⟩ :=
    SupportedOpenDerivedImage.exists_supported_perfect_complement j T hT E hE
  exact ⟨P, C, hP, hC, e, e.hom_inv_id, e.inv_hom_id⟩

/-- Closure concerns the actual original quotient in an arbitrary short exact
sequence, with the supported geometric roof supplied by its proved qcqs theorem. -/
theorem original_supported_image_quotient {U X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
    (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens) (hT : IsCompact (T : Set X))
    {S : ShortComplex (Complex U)} (hS : S.ShortExact)
    (hA : SupportedOpenDerivedImage.complexObjects j T S.X₁)
    (hB : SupportedOpenDerivedImage.complexObjects j T S.X₂) :
    SupportedOpenDerivedImage.complexObjects j T S.X₃ :=
  SupportedOpenDerivedImage.complexObjects_quotient_of_shortExact j T
    (OpenDerivedImage.qcqs_hasSupportedDerivedRoofs j T hT) hS hA hB

/-- The full supported-image inclusion reflects the actual supported
cofibration of the unchanged original arrow. -/
theorem original_supported_image_cofibration {U X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
    (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens) (hT : IsCompact (T : Set X))
    {P Q : SupportedOpenDerivedImage.ComplexObj j T} (f : P ⟶ Q) :
    let : Fact (OpenDerivedImage.HasSupportedDerivedRoofs j T) :=
      ⟨OpenDerivedImage.qcqs_hasSupportedDerivedRoofs j T hT⟩
    (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).cof
        ((SupportedOpenDerivedImage.inclusion j T).map f) ↔
      (SupportedOpenDerivedImage.complexWaldhausen j T).cof f := by
  let : Fact (OpenDerivedImage.HasSupportedDerivedRoofs j T) :=
    ⟨OpenDerivedImage.qcqs_hasSupportedDerivedRoofs j T hT⟩
  exact SupportedOpenDerivedImage.inclusion_cof_iff j T f

end Quillen.Tests.SupportedOpenFoundations
