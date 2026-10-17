/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.OpenDerivedImage.Closure
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Extension
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic

/-!
# Exact full category of the derived restriction image

The actual image is stable under the stated shifts and, under the unchanged derived-roof
hypothesis, inherited exact sequences and finite products. Inclusion and corestriction
retain their original complexes.
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
namespace Quillen.PerfectComplexes.OpenDerivedImage
attribute [local instance] HasDerivedCategory.standard Abelian.hasFiniteBiproducts
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

instance complexObjects_closedUnderIsomorphisms : (complexObjects j).IsClosedUnderIsomorphisms where
  of_iso e h := (complexObjects_iff_of_derivedIso j
    ((DerivedCategory.Q (C := U.Modules)).mapIso e)).mp h

instance complexObjects_containsZero : (complexObjects j).ContainsZero where
  exists_zero := ⟨0, isZero_zero _,
    (derivedObjects j).prop_of_isZero ((DerivedCategory.Q (C := U.Modules)).map_isZero
      (isZero_zero _))⟩

/-- The original shifted complex stays in the actual derived image. -/
theorem complexObjects_shift {E : CochainComplex U.Modules ℤ} (hE : complexObjects j E) (n : ℤ) :
    complexObjects j (E⟦n⟧) := by
  have h : derivedObjects j (((DerivedCategory.Q (C := U.Modules)).obj E)⟦n⟧) :=
    (derivedObjects j).le_shift _ _ hE
  exact (derivedObjects j).prop_of_iso (((DerivedCategory.Q
    (C := U.Modules)).commShiftIso n).app E).symm h

variable [Fact (HasDerivedRoofs j)]

instance complexObjects_extensionClosed :
    (abelianExactStructure (CochainComplex U.Modules ℤ)).IsExtensionClosed (complexObjects j) where
  prop_middle := complexObjects_of_shortExact j (Fact.out : HasDerivedRoofs j)

instance complexObjects_closedUnderFiniteProducts : (complexObjects j).IsClosedUnderFiniteProducts
  :=
  (abelianExactStructure (CochainComplex U.Modules ℤ)).extensionClosed_finiteProducts
    (complexObjects j)

/-- The actual full subcategory with one underlying chain-complex wrapper. -/
abbrev ComplexObj := (complexObjects j).FullSubcategory

/-- Actual image inclusion into original perfect complexes. -/
def inclusion : ComplexObj j ⥤ Perfect U := ObjectProperty.ιOfLE (fun _ h => locallyPerfect_of_mem j
  h)

/-- The original restriction functor with its literal image witness. -/
def complexCorestrict : Perfect X ⥤ ComplexObj j :=
  (complexObjects j).lift ((locallyPerfect X).ι ⋙ restrict j)
    (fun A => ⟨A.obj, A.property, ⟨Iso.refl _⟩⟩)

instance complexCorestrict_additive : (complexCorestrict j).Additive := by
  unfold complexCorestrict
  infer_instance

/-- The genuine actual exact-subcategory restriction functor. -/
def exactCorestrict : CategoryTheory.ExactCategory.ExactFunctor (ExactSubcategory.exactStructure
  (abelianExactStructure
  (CochainComplex X.Modules ℤ)) (locallyPerfect X))
    (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex U.Modules ℤ))
      (complexObjects j)) where
  toFunctor := complexCorestrict j
  map_conflation S hS := by
    change ((S.map (locallyPerfect X).ι).map (restrict j)).ShortExact
    exact hS.map_of_exact _

end Quillen.PerfectComplexes.OpenDerivedImage

end

end
