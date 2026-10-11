/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenWeakImage
public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedRightFractions

/-! # The original derived-saturated restriction image

This is an actual full subcategory of the original perfect chain category.
Its objects retain an isomorphism in the ORIGINAL ambient derived category.
No quasi-isomorphism from a restriction to the unchanged target is inferred.
The explicit geometric complement belongs to this derived-saturated image;
closure and approximation are established separately from actual roofs.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex TopologicalSpace
universe u
namespace Quillen.PerfectComplexes.OpenDerivedImage
attribute [local instance] HasDerivedCategory.standard
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The original derived restriction image, on actual ambient chain complexes. -/
def complexObjects : ObjectProperty (Complex U) := fun E =>
  ∃ P : Complex X, locallyPerfect X P ∧
    Nonempty ((toDerived U).obj ((restrict j).obj P) ≅ (toDerived U).obj E)

/-- Membership is invariant under the specified original derived isomorphism. -/
theorem complexObjects_iff_of_derivedIso {E E' : Complex U}
    (e : (toDerived U).obj E ≅ (toDerived U).obj E') :
    complexObjects j E ↔ complexObjects j E' := by
  constructor
  · rintro ⟨P, hP, ⟨eP⟩⟩
    exact ⟨P, hP, ⟨eP ≪≫ e⟩⟩
  · rintro ⟨P, hP, ⟨eP⟩⟩
    exact ⟨P, hP, ⟨eP ≪≫ e.symm⟩⟩

/-- Both directions of weak repleteness hold on unchanged original chain maps. -/
theorem complexObjects_iff_of_quasiIso {E E' : Complex U}
    (f : E ⟶ E') [QuasiIso f] : complexObjects j E ↔ complexObjects j E' :=
  complexObjects_iff_of_derivedIso j (asIso ((toDerived U).map f))

/-- Every actual image object is locally perfect, proved through the original isomorphism. -/
theorem locallyPerfect_of_mem {E : Complex U} (hE : complexObjects j E) : locallyPerfect U E := by
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

/-- A one-arrow witnessed object belongs to the saturated target. -/
theorem of_weakImage {E : Perfect U}
    (hE : Waldhausen.ApproximationImage.objects (perfectWaldhausen U) (perfectRestrict j) E) :
    objects j E := by
  obtain ⟨P, q, hq⟩ := hE
  have : QuasiIso q.hom := hq
  exact ⟨P.obj, P.property, ⟨asIso ((toDerived U).map q.hom)⟩⟩

/-- A supplied derived-image witness gives an actual weak cospan. The arrows
point to the new target, as required for dual approximation. -/
theorem exists_weak_cospan {E : Complex U} (hE : complexObjects j E) :
    ∃ (P : Complex X) (M : Complex U) (p : (restrict j).obj P ⟶ M) (s : E ⟶ M),
      locallyPerfect X P ∧ locallyPerfect U M ∧ QuasiIso p ∧ QuasiIso s := by
  obtain ⟨P, hP, ⟨e⟩⟩ := hE
  obtain ⟨M, p, s, hs, he⟩ := toDerived_left_fraction e.hom
  have hp : IsIso ((toDerived U).map p) := by rw [← he]; infer_instance
  exact ⟨P, M, p, s, hP,
    (locallyPerfect_iff_of_quasiIso s).mp (locallyPerfect_of_mem j ⟨P, hP, ⟨e⟩⟩),
    (DerivedCategory.isIso_Q_map_iff_quasiIso U.Modules p).mp hp, hs⟩

end Quillen.PerfectComplexes.OpenDerivedImage
