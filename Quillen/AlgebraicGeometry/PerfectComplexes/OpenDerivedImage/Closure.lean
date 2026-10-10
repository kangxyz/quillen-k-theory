/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.Roofs
public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedPerfect

/-! # Genuine cone and short-exact closure from actual open-derived roofs

Only the displayed geometric roof property is assumed. Its actual global
cone supplies the original distinguished third vertex, so closure never
requires an unproved global representative for an arbitrary open object.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open scoped ZeroObject
universe u
namespace Quillen.PerfectComplexes.OpenDerivedImage
attribute [local instance] HasDerivedCategory.standard
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The same actual restriction image on original ambient derived objects. -/
def derivedObjects : ObjectProperty (Derived U) := fun E =>
  ∃ P : Complex X, locallyPerfect X P ∧
    Nonempty ((toDerived U).obj ((restrict j).obj P) ≅ E)

@[simp] theorem derivedObjects_toDerived_iff (E : Complex U) :
    derivedObjects j ((toDerived U).obj E) ↔ complexObjects j E := Iff.rfl

instance : (derivedObjects j).IsClosedUnderIsomorphisms where
  of_iso e := by
    rintro ⟨P, hP, ⟨eP⟩⟩
    exact ⟨P, hP, ⟨eP ≪≫ e⟩⟩

instance : (derivedObjects j).ContainsZero where
  exists_zero := ⟨(toDerived U).obj ((restrict j).obj 0),
    (toDerived U).map_isZero ((restrict j).map_isZero (isZero_zero _)),
    0, (locallyPerfect X).prop_zero, ⟨Iso.refl _⟩⟩

instance : (derivedObjects j).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨by
    rintro E ⟨P, hP, ⟨eP⟩⟩
    exact ⟨P⟦n⟧, locallyPerfect_shift hP n,
      ⟨(toDerived U).mapIso (((restrict j).commShiftIso n).app P) ≪≫
        ((toDerived U).commShiftIso n).app ((restrict j).obj P) ≪≫
        (shiftFunctor _ n).mapIso eP⟩⟩⟩

/-- The actual cone of the supplied global numerator represents the third
vertex of the original open triangle, via the displayed locally weak denominator. -/
theorem triangulatedClosed₃ (hroof : HasDerivedRoofs j) :
    (derivedObjects j).IsTriangulatedClosed₃ := .mk' (by
  rintro T hT ⟨P, hP, ⟨eP⟩⟩ ⟨K, hK, ⟨eK⟩⟩
  let α := eP.hom ≫ T.mor₁ ≫ eK.inv
  obtain ⟨P', q, g, hP', hq, hg⟩ := hroof P K hP hK α
  let eP' := asIso ((toDerived U).map ((restrict j).map q)) ≪≫ eP
  refine ⟨CochainComplex.mappingCone g, locallyPerfect_mappingCone hP' hK g, ⟨?_⟩⟩
  refine (toDerived U).mapIso (CochainComplex.mappingCone.mapHomologicalComplexIso g
      (Scheme.Modules.restrictFunctor j)) ≪≫ ?_
  exact Triangle.π₃.mapIso (isoTriangleOfIso₁₂ _ T
    (mappingConeTriangle_distinguished ((restrict j).map g)) hT eP' eK (by
      change (toDerived U).map ((restrict j).map g) ≫ eK.hom = _
      rw [← hg]
      simp only [α, eP', Iso.trans_hom, asIso_hom, Category.assoc,
        Iso.inv_hom_id, Category.comp_id]
      )))

/-- Original distinguished extension closure, derived from the proved cone construction. -/
theorem triangulatedClosed₂ (hroof : HasDerivedRoofs j) :
    (derivedObjects j).IsTriangulatedClosed₂ := by
  let := triangulatedClosed₃ j hroof
  exact .of_isTriangulatedClosed₃

/-- Original distinguished kernel closure, including the exact rotation shift. -/
theorem triangulatedClosed₁ (hroof : HasDerivedRoofs j) :
    (derivedObjects j).IsTriangulatedClosed₁ := by
  let := triangulatedClosed₂ j hroof
  let : (derivedObjects j).IsTriangulated := {}
  infer_instance

/-- The genuine original ambient short exact sequence supplies extension closure. -/
theorem complexObjects_of_shortExact (hroof : HasDerivedRoofs j)
    {S : ShortComplex (Complex U)} (hS : S.ShortExact)
    (h₁ : complexObjects j S.X₁) (h₃ : complexObjects j S.X₃) :
    complexObjects j S.X₂ := by
  let := triangulatedClosed₂ j hroof
  exact (derivedObjects j).ext_of_isTriangulatedClosed₂ (shortExactTriangle hS)
    (shortExactTriangle_distinguished hS) h₁ h₃

/-- The actual cofiber, not a replacement object, belongs to the image. -/
theorem complexObjects_quotient_of_shortExact (hroof : HasDerivedRoofs j)
    {S : ShortComplex (Complex U)} (hS : S.ShortExact)
    (h₁ : complexObjects j S.X₁) (h₂ : complexObjects j S.X₂) :
    complexObjects j S.X₃ := by
  let := triangulatedClosed₃ j hroof
  exact (derivedObjects j).ext_of_isTriangulatedClosed₃ (shortExactTriangle hS)
    (shortExactTriangle_distinguished hS) h₁ h₂

/-- The actual kernel endpoint belongs to the image when the other endpoints do. -/
theorem complexObjects_kernel_of_shortExact (hroof : HasDerivedRoofs j)
    {S : ShortComplex (Complex U)} (hS : S.ShortExact)
    (h₂ : complexObjects j S.X₂) (h₃ : complexObjects j S.X₃) :
    complexObjects j S.X₁ := by
  let := triangulatedClosed₁ j hroof
  exact (derivedObjects j).ext_of_isTriangulatedClosed₁ (shortExactTriangle hS)
    (shortExactTriangle_distinguished hS) h₂ h₃

end Quillen.PerfectComplexes.OpenDerivedImage
