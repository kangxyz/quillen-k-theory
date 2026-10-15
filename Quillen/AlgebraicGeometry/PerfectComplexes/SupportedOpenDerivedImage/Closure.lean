/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportCone
public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpenDerivedImage.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.SupportedRoofs
public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedPerfect

/-!
# Genuine triangulated closure of the supported restriction image

A support-preserving original derived roof supplies a global numerator cone
representing the third vertex of an original distinguished triangle. The
actual cone remains supported. Shifts and rotations then give genuine
extension, quotient, and kernel closure for the original short exact
sequences. The precise roof property is explicit in these reusable closure
lemmas; its qcqs geometric proof is provided by the imported SupportedRoofs.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open scoped ZeroObject
universe u
namespace Quillen.PerfectComplexes.SupportedOpenDerivedImage
attribute [local instance] HasDerivedCategory.standard
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

/-- The same actual restriction image on original ambient derived objects. -/
def derivedObjects : ObjectProperty (Derived U) := fun E =>
  ∃ P : Complex X, perfectSupported T.ι P ∧
    Nonempty ((toDerived U).obj ((restrict j).obj P) ≅ E)

@[simp] theorem derivedObjects_toDerived_iff (E : Complex U) :
    derivedObjects j T ((toDerived U).obj E) ↔ complexObjects j T E := Iff.rfl

instance : (derivedObjects j T).IsClosedUnderIsomorphisms where
  of_iso e := by
    rintro ⟨P, hP, ⟨eP⟩⟩
    exact ⟨P, hP, ⟨eP ≪≫ e⟩⟩

instance : (derivedObjects j T).ContainsZero where
  exists_zero := ⟨(toDerived U).obj ((restrict j).obj 0),
    (toDerived U).map_isZero ((restrict j).map_isZero (isZero_zero _)),
    0, (perfectSupported T.ι).prop_zero, ⟨Iso.refl _⟩⟩

instance : (derivedObjects j T).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨by
    rintro E ⟨P, hP, ⟨eP⟩⟩
    exact ⟨P⟦n⟧, perfectSupported_shift T.ι hP n,
      ⟨(toDerived U).mapIso (((restrict j).commShiftIso n).app P) ≪≫
        ((toDerived U).commShiftIso n).app ((restrict j).obj P) ≪≫
        (shiftFunctor _ n).mapIso eP⟩⟩⟩

/-- The actual cone of the supplied global numerator represents the third
vertex of the original open triangle, via the displayed locally weak denominator. -/
theorem triangulatedClosed₃ (hroof : OpenDerivedImage.HasSupportedDerivedRoofs j T) :
    (derivedObjects j T).IsTriangulatedClosed₃ := .mk' (by
  rintro Δ hΔ ⟨P, hP, ⟨eP⟩⟩ ⟨K, hK, ⟨eK⟩⟩
  let α := eP.hom ≫ Δ.mor₁ ≫ eK.inv
  obtain ⟨P', q, g, hP', hq, hg, hzP'⟩ := hroof P K hP.1 hK.1
    ((isZero_toDerived_iff_acyclic _).mpr hP.2)
    ((isZero_toDerived_iff_acyclic _).mpr hK.2) α
  have hP'S : perfectSupported T.ι P' := ⟨hP', (isZero_toDerived_iff_acyclic _).mp hzP'⟩
  let eP' := asIso ((toDerived U).map ((restrict j).map q)) ≪≫ eP
  refine ⟨CochainComplex.mappingCone g, perfectSupported_mappingCone T.ι hP'S hK g, ⟨?_⟩⟩
  refine (toDerived U).mapIso (CochainComplex.mappingCone.mapHomologicalComplexIso g
      (Scheme.Modules.restrictFunctor j)) ≪≫ ?_
  exact Triangle.π₃.mapIso (isoTriangleOfIso₁₂ _ Δ
    (mappingConeTriangle_distinguished ((restrict j).map g)) hΔ eP' eK (by
      change (toDerived U).map ((restrict j).map g) ≫ eK.hom = _
      rw [← hg]
      simp only [α, eP', Iso.trans_hom, asIso_hom, Category.assoc,
        Iso.inv_hom_id, Category.comp_id]
      )))

/-- Original distinguished extension closure, derived from the proved cone construction. -/
theorem triangulatedClosed₂ (hroof : OpenDerivedImage.HasSupportedDerivedRoofs j T) :
    (derivedObjects j T).IsTriangulatedClosed₂ := by
  let := triangulatedClosed₃ j T hroof
  exact .of_isTriangulatedClosed₃

/-- Original distinguished kernel closure, including the exact rotation shift. -/
theorem triangulatedClosed₁ (hroof : OpenDerivedImage.HasSupportedDerivedRoofs j T) :
    (derivedObjects j T).IsTriangulatedClosed₁ := by
  let := triangulatedClosed₂ j T hroof
  let : (derivedObjects j T).IsTriangulated := {}
  infer_instance

/-- The genuine original ambient short exact sequence supplies extension closure. -/
theorem complexObjects_of_shortExact (hroof : OpenDerivedImage.HasSupportedDerivedRoofs j T)
    {S : ShortComplex (Complex U)} (hS : S.ShortExact)
    (h₁ : complexObjects j T S.X₁) (h₃ : complexObjects j T S.X₃) :
    complexObjects j T S.X₂ := by
  let := triangulatedClosed₂ j T hroof
  exact (derivedObjects j T).ext_of_isTriangulatedClosed₂ (shortExactTriangle hS)
    (shortExactTriangle_distinguished hS) h₁ h₃

/-- The actual cofiber, not a replacement object, belongs to the image. -/
theorem complexObjects_quotient_of_shortExact (hroof : OpenDerivedImage.HasSupportedDerivedRoofs j
  T)
    {S : ShortComplex (Complex U)} (hS : S.ShortExact)
    (h₁ : complexObjects j T S.X₁) (h₂ : complexObjects j T S.X₂) :
    complexObjects j T S.X₃ := by
  let := triangulatedClosed₃ j T hroof
  exact (derivedObjects j T).ext_of_isTriangulatedClosed₃ (shortExactTriangle hS)
    (shortExactTriangle_distinguished hS) h₁ h₂

/-- The actual kernel endpoint belongs to the image when the other endpoints do. -/
theorem complexObjects_kernel_of_shortExact (hroof : OpenDerivedImage.HasSupportedDerivedRoofs j T)
    {S : ShortComplex (Complex U)} (hS : S.ShortExact)
    (h₂ : complexObjects j T S.X₂) (h₃ : complexObjects j T S.X₃) :
    complexObjects j T S.X₁ := by
  let := triangulatedClosed₁ j T hroof
  exact (derivedObjects j T).ext_of_isTriangulatedClosed₁ (shortExactTriangle hS)
    (shortExactTriangle_distinguished hS) h₂ h₃

end Quillen.PerfectComplexes.SupportedOpenDerivedImage
