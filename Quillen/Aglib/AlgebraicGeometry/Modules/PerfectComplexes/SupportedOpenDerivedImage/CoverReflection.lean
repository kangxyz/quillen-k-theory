/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.OpenGluing.Supported
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.SupportedOpenDerivedImage.Basic
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Restriction
/-! # Supported derived image reflection on a genuine covering pair -/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules (derivedRestrict derivedRestrictFactors)

open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open scoped ZeroObject
universe u
attribute [local instance] Scheme.Modules.standardHasDerivedCategory
namespace Quillen.PerfectComplexes.SupportedOpenDerivedImage
attribute [local instance] HasDerivedCategory.standard
variable {V X : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j] (T Z : X.Opens)
  (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ T)

include hcover in
/-- Supported extension of the actual overlap restriction is equivalent to extension
of the original supported perfect complex. The reverse implication glues the specified
derived isomorphism, without replacing it by an assumed weak arrow. -/
theorem complexObjects_cover_iff (E : CochainComplex T.toScheme.Modules ℤ)
    (hE : perfectSupported (T.ι ⁻¹ᵁ Z).ι E) :
    complexObjects T.ι Z E ↔
      complexObjects (j ⁻¹ᵁ T).ι (j ⁻¹ᵁ Z) ((restrict (j.resLE T (j ⁻¹ᵁ T) le_rfl)).obj E) := by
  let a := j.resLE T (j ⁻¹ᵁ T) le_rfl
  let b := (j ⁻¹ᵁ T).ι
  have hs : a ≫ T.ι = b ≫ j := j.resLE_comp_ι le_rfl
  constructor
  · rintro ⟨P,hP,⟨e⟩⟩
    refine ⟨(restrict j).obj P,perfectSupported_restrict j Z hP,⟨?_⟩⟩
    exact (DerivedCategory.Q (C := (j ⁻¹ᵁ T).toScheme.Modules)).mapIso
      ((openSquareRestrictIso a b T.ι j hs).app P).symm ≪≫
        (derivedRestrictFactors a).symm.app ((restrict T.ι).obj P) ≪≫
        (derivedRestrict a).mapIso e ≪≫
        (derivedRestrictFactors a).app E
  · rintro ⟨B,hB,⟨e⟩⟩
    obtain ⟨P,hP,u,v,hu,hv⟩ := exists_supported_glue_of_openSquare a b T.ι j hs
      (by
        intro x hx
        obtain ⟨y,hy⟩ := hx
        refine ⟨⟨y,?_⟩,?_⟩
        · change j y ∈ T
          rw [hy]
          exact x.property
        · apply Subtype.ext
          simpa [a] using hy)
      (by
        intro x hx
        obtain ⟨y,hy⟩ := hx
        exact ⟨⟨x,by change j x ∈ T; rw [←hy]; exact y.property⟩,rfl⟩)
      (fun x ↦ (hcover x).symm.imp (fun hx ↦ ⟨⟨x,hx⟩,rfl⟩) id)
      Z E B hE hB e.symm
    exact ⟨P,hP,⟨(asIso ((DerivedCategory.Q (C := T.toScheme.Modules)).map u)).symm⟩⟩

end Quillen.PerfectComplexes.SupportedOpenDerivedImage
