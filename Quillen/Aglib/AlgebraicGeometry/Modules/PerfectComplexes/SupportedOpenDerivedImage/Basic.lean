/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Support.Restriction
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.GlobalSupportedDensity
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Restriction
/-!
# Original derived restriction image with prescribed support

The image consists of original complexes derived-isomorphic to restriction
of actual global perfect complexes vanishing on a specified open T. Every
such target retains the support on j⁻¹T. Membership is invariant under the
original derived isomorphisms and actual quasi-isomorphisms.

For qcqs base, compact open source and compact T, the genuine global
supported-complement theorem gives an actual supported perfect complement.
Its support is proved using the original derived biproduct retraction.
No one-arrow replacement into an arbitrary all-sheaf target is asserted.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
attribute [local instance] Scheme.Modules.standardHasDerivedCategory
namespace Quillen.PerfectComplexes.SupportedOpenDerivedImage
attribute [local instance] HasDerivedCategory.standard Abelian.hasFiniteBiproducts
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

/-- The actual restriction image of globally perfect complexes with the
specified support, saturated in the original derived category only. -/
def complexObjects : ObjectProperty (CochainComplex U.Modules ℤ) := fun E =>
  ∃ P : CochainComplex X.Modules ℤ, perfectSupported T.ι P ∧
    Nonempty ((DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj P) ≅
      (DerivedCategory.Q (C := U.Modules)).obj E)

lemma complexObjects_iff_of_derivedIso {E E' : CochainComplex U.Modules ℤ}
    (e : (DerivedCategory.Q (C := U.Modules)).obj E ≅ (DerivedCategory.Q (C := U.Modules)).obj E') :
    complexObjects j T E ↔ complexObjects j T E' := by
  constructor
  · rintro ⟨P, hP, ⟨eP⟩⟩
    exact ⟨P, hP, ⟨eP ≪≫ e⟩⟩
  · rintro ⟨P, hP, ⟨eP⟩⟩
    exact ⟨P, hP, ⟨eP ≪≫ e.symm⟩⟩

lemma complexObjects_iff_of_quasiIso {E E' : CochainComplex U.Modules ℤ} (f : E ⟶ E') [QuasiIso f] :
    complexObjects j T E ↔ complexObjects j T E' :=
  complexObjects_iff_of_derivedIso j T (asIso ((DerivedCategory.Q (C := U.Modules)).map f))

/-- Every actual saturated-image object retains genuine support after
restriction along the original inverse-image support inclusion. -/
lemma perfectSupported_of_mem {E : CochainComplex U.Modules ℤ} (hE : complexObjects j T E) :
    perfectSupported (j ⁻¹ᵁ T).ι E := by
  obtain ⟨P, hP, ⟨e⟩⟩ := hE
  have hP' := perfectSupported_restrict j T hP
  refine ⟨(locallyPerfect_iff_of_derivedIso e).mp hP'.1, ?_⟩
  rw [← isZero_toDerived_iff_acyclic]
  exact ((isZero_toDerived_iff_acyclic _).mpr hP'.2).of_iso
    (restrictDerivedIso (j ⁻¹ᵁ T).ι e).symm

/-- The full supported-image subcategory uses the existing supported objects
and the same original chain morphisms. -/
def objects : ObjectProperty (perfectSupported (j ⁻¹ᵁ T).ι).FullSubcategory :=
  fun E => complexObjects j T E.obj

/-- The original supported restriction belongs to its actual saturated image. -/
lemma obj_mem (P : (perfectSupported T.ι).FullSubcategory) :
    objects j T ((perfectSupportedRestrict j T).obj P) :=
  ⟨P.obj, P.property, ⟨Iso.refl _⟩⟩

/-- Genuine global supported density gives an actual supported complement;
both summands retain the original support on the overlap. -/
lemma exists_supported_perfect_complement [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace U] (hT : IsCompact (T : Set X))
    (E : CochainComplex U.Modules ℤ) (hE : perfectSupported (j ⁻¹ᵁ T).ι E) :
    ∃ C : CochainComplex U.Modules ℤ, perfectSupported (j ⁻¹ᵁ T).ι C ∧ complexObjects j T
      (C ⊞ E) := by
  obtain ⟨P, C, hP, hC, ⟨e⟩, hPT⟩ :=
    locallyPerfect_exists_global_supported_perfect_complement_of_openImmersion j E hE.1 T hT
      ((isZero_toDerived_iff_acyclic _).mpr hE.2)
  have hP' : perfectSupported T.ι P := ⟨hP, (isZero_toDerived_iff_acyclic _).mp hPT⟩
  have hsum : IsZero ((DerivedCategory.Q (C := (j ⁻¹ᵁ T).toScheme.Modules)).obj
      ((restrict (j ⁻¹ᵁ T).ι).obj (E ⊞ C))) :=
    (isZero_restrict_preimage_of_isZero j T P hPT).of_iso
      (restrictDerivedIso (j ⁻¹ᵁ T).ι e).symm
  have hC' : perfectSupported (j ⁻¹ᵁ T).ι C := by
    refine ⟨hC, (isZero_toDerived_iff_acyclic _).mp ?_⟩
    let r : Retract C (E ⊞ C) :=
      { i := biprod.inr, r := biprod.snd, retract := biprod.inr_snd }
    let r' := r.map (restrict (j ⁻¹ᵁ T).ι ⋙ DerivedCategory.Q (C := (j ⁻¹ᵁ T).toScheme.Modules))
    rw [IsZero.iff_id_eq_zero]
    calc
      _ = r'.i ≫ r'.r := r'.retract.symm
      _ = 0 := by rw [hsum.eq_of_tgt r'.i 0, zero_comp]
  exact ⟨C, hC', P, hP', ⟨e ≪≫ (DerivedCategory.Q (C := U.Modules)).mapIso (biprod.braiding E C)⟩⟩

end Quillen.PerfectComplexes.SupportedOpenDerivedImage
