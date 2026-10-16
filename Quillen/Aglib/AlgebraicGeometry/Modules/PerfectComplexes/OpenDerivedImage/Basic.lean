/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalRestriction
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.RestrictionHom
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic

/-!
# Derived-saturated open restriction image

Original complexes retain an actual isomorphism in the ambient derived category to the restriction of a global locally perfect complex. The full category, corestriction, and genuine weak cospans preserve every chain map.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex TopologicalSpace
universe u
attribute [local instance] Scheme.Modules.standardHasDerivedCategory
namespace Quillen.PerfectComplexes.OpenDerivedImage
attribute [local instance] HasDerivedCategory.standard
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The original derived restriction image, on actual ambient chain complexes. -/
def complexObjects : ObjectProperty (CochainComplex U.Modules ℤ) := fun E =>
  ∃ P : CochainComplex X.Modules ℤ, locallyPerfect X P ∧
    Nonempty ((DerivedCategory.Q (C := U.Modules)).obj ((restrict j).obj P) ≅
      (DerivedCategory.Q (C := U.Modules)).obj E)

/-- Membership is invariant under the specified original derived isomorphism. -/
theorem complexObjects_iff_of_derivedIso {E E' : CochainComplex U.Modules ℤ}
    (e : (DerivedCategory.Q (C := U.Modules)).obj E ≅ (DerivedCategory.Q (C := U.Modules)).obj E') :
    complexObjects j E ↔ complexObjects j E' := by
  constructor
  · rintro ⟨P, hP, ⟨eP⟩⟩
    exact ⟨P, hP, ⟨eP ≪≫ e⟩⟩
  · rintro ⟨P, hP, ⟨eP⟩⟩
    exact ⟨P, hP, ⟨eP ≪≫ e.symm⟩⟩

/-- Both directions of weak repleteness hold on unchanged original chain maps. -/
theorem complexObjects_iff_of_quasiIso {E E' : CochainComplex U.Modules ℤ}
    (f : E ⟶ E') [QuasiIso f] : complexObjects j E ↔ complexObjects j E' :=
  complexObjects_iff_of_derivedIso j (asIso ((DerivedCategory.Q (C := U.Modules)).map f))

/-- Every actual image object is locally perfect, proved through the original isomorphism. -/
theorem locallyPerfect_of_mem {E : CochainComplex U.Modules ℤ}
    (hE : complexObjects j E) : locallyPerfect U E := by
  obtain ⟨P, hP, ⟨e⟩⟩ := hE
  exact (locallyPerfect_iff_of_derivedIso e).mp (locallyPerfect_restrict j hP)

/-- The full subcategory retains all original perfect-complex morphisms. -/
def objects : ObjectProperty (Perfect U) := fun E => complexObjects j E.obj
/-- The full category of original perfect complexes in the saturated derived restriction image. -/
abbrev Obj := (objects j).FullSubcategory

/-- Original restriction has its literal reflexive derived-image witness. -/
theorem obj_mem (P : Perfect X) : objects j ((perfectRestrict j).obj P) :=
  ⟨P.obj, P.property, ⟨Iso.refl _⟩⟩

/-- The original restriction corestricts without changing any underlying arrow. -/
def corestrict : Perfect X ⥤ Obj j := (objects j).lift (perfectRestrict j) (obj_mem j)

/-- A supplied derived-image witness gives an actual weak cospan. The arrows
point to the new target, as required for dual approximation. -/
theorem exists_weak_cospan {E : CochainComplex U.Modules ℤ} (hE : complexObjects j E) :
    ∃ (P : CochainComplex X.Modules ℤ) (M : CochainComplex U.Modules ℤ) (p : (restrict j).obj P ⟶ M)
      (s : E ⟶ M),
      locallyPerfect X P ∧ locallyPerfect U M ∧ QuasiIso p ∧ QuasiIso s := by
  obtain ⟨P, hP, ⟨e⟩⟩ := hE
  obtain ⟨M, p, s, hDenIso1, hFac1⟩ := DerivedCategory.left_fac e.hom
  have hs : QuasiIso s :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).1 hDenIso1
  have he : (e.hom) ≫ DerivedCategory.Q.map s = DerivedCategory.Q.map p := by
    let := hDenIso1
    rw [hFac1, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hp : IsIso ((DerivedCategory.Q (C := U.Modules)).map p) := by rw [← he]; infer_instance
  exact ⟨P, M, p, s, hP,
    (locallyPerfect_iff_of_quasiIso s).mp (locallyPerfect_of_mem j ⟨P, hP, ⟨e⟩⟩),
    (DerivedCategory.isIso_Q_map_iff_quasiIso U.Modules p).mp hp, hs⟩

end Quillen.PerfectComplexes.OpenDerivedImage

end

end
