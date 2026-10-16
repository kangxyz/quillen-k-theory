/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.SupportedOpenDerivedImage.Closure
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic

/-!
# Exact category of the supported derived restriction image

Actual support and the prescribed supported-roof hypothesis give the original shift, zero, isomorphism, extension and finite-product closure, full inclusion and exact corestriction.
-/
@[expose] public section



open AlgebraicGeometry.Scheme.Modules.Complex


open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex Opposite
open scoped ZeroObject
universe u
attribute [local instance] Scheme.Modules.standardHasDerivedCategory
namespace Quillen.PerfectComplexes.SupportedOpenDerivedImage
attribute [local instance] HasDerivedCategory.standard Abelian.hasFiniteBiproducts
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

instance complexObjects_closedUnderIsomorphisms : (complexObjects j T).IsClosedUnderIsomorphisms
  where
  of_iso e h := (complexObjects_iff_of_derivedIso j T
    ((DerivedCategory.Q (C := U.Modules)).mapIso e)).mp h

instance complexObjects_containsZero : (complexObjects j T).ContainsZero where
  exists_zero := ⟨0, isZero_zero _,
    (derivedObjects j T).prop_of_isZero ((DerivedCategory.Q (C := U.Modules)).map_isZero
      (isZero_zero _))⟩

/-- The original shifted complex stays in the actual derived image. -/
theorem complexObjects_shift {E : CochainComplex U.Modules ℤ} (hE : complexObjects j T E) (n : ℤ) :
    complexObjects j T (E⟦n⟧) := by
  have h : derivedObjects j T (((DerivedCategory.Q (C := U.Modules)).obj E)⟦n⟧) :=
    (derivedObjects j T).le_shift _ _ hE
  exact (derivedObjects j T).prop_of_iso (((DerivedCategory.Q
    (C := U.Modules)).commShiftIso n).app E).symm h

variable [Fact (OpenDerivedImage.HasSupportedDerivedRoofs j T)]

instance complexObjects_extensionClosed :
    (abelianExactStructure (CochainComplex U.Modules ℤ)).IsExtensionClosed
      (complexObjects j T) where
  prop_middle := complexObjects_of_shortExact j T (Fact.out :
    OpenDerivedImage.HasSupportedDerivedRoofs j T)

instance complexObjects_closedUnderFiniteProducts : (complexObjects j T).IsClosedUnderFiniteProducts
  :=
  (abelianExactStructure (CochainComplex U.Modules ℤ)).extensionClosed_finiteProducts
    (complexObjects j T)

/-- The actual full subcategory with one underlying chain-complex wrapper. -/
abbrev ComplexObj := (complexObjects j T).FullSubcategory

/-- Actual image inclusion into original perfect complexes. -/
def inclusion : ComplexObj j T ⥤ (perfectSupported (j ⁻¹ᵁ T).ι).FullSubcategory :=
  ObjectProperty.ιOfLE (fun _ h => perfectSupported_of_mem j T h)

/-- The original restriction functor with its literal image witness. -/
def complexCorestrict : (perfectSupported T.ι).FullSubcategory ⥤ ComplexObj j T :=
  (complexObjects j T).lift ((perfectSupported T.ι).ι ⋙ restrict j)
    (fun A => ⟨A.obj, A.property, ⟨Iso.refl _⟩⟩)

instance complexCorestrict_additive : (complexCorestrict j T).Additive := by
  unfold complexCorestrict
  infer_instance

/-- The genuine actual exact-subcategory restriction functor. -/
def exactCorestrict : CategoryTheory.ExactCategory.ExactFunctor (ExactSubcategory.exactStructure
  (abelianExactStructure
  (CochainComplex X.Modules ℤ)) (perfectSupported T.ι))
    (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex U.Modules ℤ))
      (complexObjects j T)) where
  toFunctor := complexCorestrict j T
  map_conflation S hS := by
    change ((S.map (perfectSupported T.ι).ι).map (restrict j)).ShortExact
    exact hS.map_of_exact _

end Quillen.PerfectComplexes.SupportedOpenDerivedImage

end

end
