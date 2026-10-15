/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.RestrictionComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.GlobalDense
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenGluing.AffineExtension

/-! # Derived image reflection on a genuine covering pair -/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open scoped ZeroObject
universe u
namespace Quillen.PerfectComplexes.OpenDerivedImage
attribute [local instance] HasDerivedCategory.standard
variable {V X : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j] (T : X.Opens)
  (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ T)

include hcover in
/-- Extension of the actual overlap restriction is equivalent to extension
of the original perfect complex. The reverse implication glues the specified
derived isomorphism, without replacing it by an assumed weak arrow. -/
theorem complexObjects_cover_iff (E : Complex T.toScheme) (hE : locallyPerfect T.toScheme E) :
    complexObjects T.ι E ↔
      complexObjects (j ⁻¹ᵁ T).ι ((restrict (j.resLE T (j ⁻¹ᵁ T) le_rfl)).obj E) := by
  let a := j.resLE T (j ⁻¹ᵁ T) le_rfl
  let b := (j ⁻¹ᵁ T).ι
  have hs : a ≫ T.ι = b ≫ j := j.resLE_comp_ι le_rfl
  constructor
  · rintro ⟨P,hP,⟨e⟩⟩
    refine ⟨(restrict j).obj P,locallyPerfect_restrict j hP,⟨?_⟩⟩
    exact (toDerived (j ⁻¹ᵁ T).toScheme).mapIso
      ((openSquareRestrictIso a b T.ι j hs).app P).symm ≪≫
        (derivedRestrictFactors a).symm.app ((restrict T.ι).obj P) ≪≫
        (derivedRestrict a).mapIso e ≪≫
        (derivedRestrictFactors a).app E
  · rintro ⟨B,hB,⟨e⟩⟩
    obtain ⟨M,α,β,hα,hβ,_,_⟩ :=
      Quillen.CochainComplex.exists_weak_span_homotopy_of_derived_iso e.symm
        (0 : _ ⟶ (0 : Complex (j ⁻¹ᵁ T).toScheme)) 0 (by simp)
    let P := OpenHomotopyGluing.glued a b T.ι j hs α β
    let u := OpenHomotopyGluing.first a b T.ι j hs α β
    let v := OpenHomotopyGluing.second a b T.ι j hs α β
    have hu : QuasiIso u := OpenHomotopyGluing.first_quasiIso a b T.ι j hs α β (by
      intro x hx
      obtain ⟨y,hy⟩ := hx
      refine ⟨⟨y,?_⟩,?_⟩
      · change j y ∈ T
        rw [hy]
        exact x.property
      · apply Subtype.ext
        simpa [a] using hy)
    have hv : QuasiIso v := OpenHomotopyGluing.second_quasiIso a b T.ι j hs α β (by
      intro x hx
      obtain ⟨y,hy⟩ := hx
      exact ⟨⟨x,by change j x ∈ T; rw [←hy]; exact y.property⟩,rfl⟩)
    have hp : locallyPerfect X P := locallyPerfect_of_two_openImmersions T.ι j
      (fun x ↦ (hcover x).symm.imp (fun hx ↦ ⟨⟨x,hx⟩,rfl⟩) id)
      ((locallyPerfect_iff_of_quasiIso u).mp hE)
      ((locallyPerfect_iff_of_quasiIso v).mp hB)
    exact ⟨P,hp,⟨(asIso ((toDerived T.toScheme).map u)).symm⟩⟩

end Quillen.PerfectComplexes.OpenDerivedImage
