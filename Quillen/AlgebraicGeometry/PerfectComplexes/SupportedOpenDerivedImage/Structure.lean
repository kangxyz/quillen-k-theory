/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpenDerivedImage.Closure

/-!
# Actual Waldhausen structures on the supported restriction image

The original supported image is an extension-closed full subcategory of
actual sheaf complexes. Its Waldhausen structure and actual opposite are
constructed from inherited exact sequences and quasi-isomorphisms. The
original supported restriction corestricts exactly in both variances, and
its inclusion into the existing supported target reflects cofibrations via
genuine quotient membership. Actual opposite joint data comes from the
original complex cylinder. The exact supported roof property is explicit.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex Opposite
open scoped ZeroObject
universe u
namespace Quillen.PerfectComplexes.SupportedOpenDerivedImage
open Waldhausen Fibration
attribute [local instance] HasDerivedCategory.standard Abelian.hasFiniteBiproducts
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

instance complexObjects_closedUnderIsomorphisms : (complexObjects j T).IsClosedUnderIsomorphisms
  where
  of_iso e h := (complexObjects_iff_of_derivedIso j T ((toDerived U).mapIso e)).mp h

instance complexObjects_containsZero : (complexObjects j T).ContainsZero where
  exists_zero := ⟨0, isZero_zero _,
    (derivedObjects j T).prop_of_isZero ((toDerived U).map_isZero (isZero_zero _))⟩

/-- The original shifted complex stays in the actual derived image. -/
theorem complexObjects_shift {E : Complex U} (hE : complexObjects j T E) (n : ℤ) :
    complexObjects j T (E⟦n⟧) := by
  have h : derivedObjects j T (((toDerived U).obj E)⟦n⟧) := (derivedObjects j T).le_shift _ _ hE
  exact (derivedObjects j T).prop_of_iso (((toDerived U).commShiftIso n).app E).symm h

variable [Fact (OpenDerivedImage.HasSupportedDerivedRoofs j T)]

instance complexObjects_extensionClosed :
    (abelianExactStructure (Complex U)).IsExtensionClosed (complexObjects j T) where
  prop_middle := complexObjects_of_shortExact j T (Fact.out :
    OpenDerivedImage.HasSupportedDerivedRoofs j T)

instance complexObjects_closedUnderFiniteProducts : (complexObjects j T).IsClosedUnderFiniteProducts
  :=
  (abelianExactStructure (Complex U)).extensionClosed_finiteProducts (complexObjects j T)

/-- The actual full subcategory with one underlying chain-complex wrapper. -/
abbrev ComplexObj := (complexObjects j T).FullSubcategory

/-- Genuine original quasi-isomorphisms and inherited admissible monomorphisms. -/
def complexWaldhausen : Structure (ComplexObj j T) := complexSubcategory (complexObjects j T)

/-- Original admissible epimorphisms on the literal opposite. -/
def complexOppositeWaldhausen : Structure (ComplexObj j T)ᵒᵖ := oppositeComplexSubcategory
  (complexObjects j T)

theorem complexOpposite_compatible : IsCompatibleDual (complexWaldhausen j T)
  (complexOppositeWaldhausen j T) :=
  oppositeComplexSubcategory_compatible (complexObjects j T)

/-- Actual image inclusion into original perfect complexes. -/
def inclusion : ComplexObj j T ⥤ (perfectSupported (j ⁻¹ᵁ T).ι).FullSubcategory :=
  ObjectProperty.ιOfLE (fun _ h => perfectSupported_of_mem j T h)

theorem inclusion_exact : IsExact (complexWaldhausen j T).cof (complexWaldhausen j T).weq
    (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).cof (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).weq
      (inclusion j T) :=
  subcategoryInclusion_exact (complexObjects j T) (perfectSupported (j ⁻¹ᵁ T).ι) (fun _ h =>
    perfectSupported_of_mem j T h)

/-- Reflection retains the actual ambient perfect quotient and proves that
same quotient belongs to the derived image. -/
theorem inclusion_cof_iff {A B : ComplexObj j T} (f : A ⟶ B) :
    (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).cof ((inclusion j T).map f) ↔ (complexWaldhausen j
      T).cof f := by
  constructor
  · intro hf
    obtain ⟨Z, hZ, p, hp, hS⟩ := (ExactSubcategory.inflation_iff (abelianExactStructure (Complex U))
      (perfectSupported (j ⁻¹ᵁ T).ι) ((inclusion j T).map f)).mp hf
    apply (ExactSubcategory.inflation_iff (abelianExactStructure (Complex U)) (complexObjects j T)
      f).mpr
    exact ⟨Z, complexObjects_quotient_of_shortExact j T (Fact.out :
      OpenDerivedImage.HasSupportedDerivedRoofs j T)
      hS A.property B.property, p, hp, hS⟩
  · exact (inclusion_exact j T).cofibration f

/-- The original restriction functor with its literal image witness. -/
def complexCorestrict : (perfectSupported T.ι).FullSubcategory ⥤ ComplexObj j T :=
  (complexObjects j T).lift ((perfectSupported T.ι).ι ⋙ restrict j)
    (fun A => ⟨A.obj, A.property, ⟨Iso.refl _⟩⟩)

instance complexCorestrict_additive : (complexCorestrict j T).Additive := by
  unfold complexCorestrict
  infer_instance

/-- The genuine actual exact-subcategory restriction functor. -/
def exactCorestrict : Quillen.ExactFunctor (ExactSubcategory.exactStructure (abelianExactStructure
  (Complex X)) (perfectSupported T.ι))
    (ExactSubcategory.exactStructure (abelianExactStructure (Complex U)) (complexObjects j T)) where
  toFunctor := complexCorestrict j T
  map_conflation S hS := by
    change ((S.map (perfectSupported T.ι).ι).map (restrict j)).ShortExact
    exact hS.map_of_exact _

/-- Original restriction is genuinely exact on the saturated image. -/
theorem complexCorestrict_exact : IsExact (perfectSupportedWaldhausen T.ι).cof
  (perfectSupportedWaldhausen T.ι).weq
    (complexWaldhausen j T).cof (complexWaldhausen j T).weq (complexCorestrict j T) where
  zero h := (complexCorestrict j T).map_isZero h
  cofibration f hf := (exactCorestrict j T).map_inflation f hf
  weak f hf := by
    have : QuasiIso f.hom := hf
    exact restrict_quasiIso j f.hom
  pushout hi h := by
    apply IsPushout.of_map_of_faithful (complexObjects j T).ι
    exact (fullSubcategory_map_pushout (abelianExactStructure (Complex X))
      (perfectSupported T.ι) hi h).map (restrict j)

/-- The unchanged restriction is exact on the actual opposite structures. -/
theorem complexCorestrict_op_exact : IsExact
    (perfectSupportedOppositeWaldhausen T.ι).cof (perfectSupportedOppositeWaldhausen T.ι).weq
    (complexOppositeWaldhausen j T).cof (complexOppositeWaldhausen j T).weq (complexCorestrict j
      T).op where
  zero h := (complexCorestrict j T).op.map_isZero h
  cofibration f hf := (exactCorestrict j T).map_deflation f.unop hf
  weak f hf := by
    have : QuasiIso f.unop.hom := hf
    exact restrict_quasiIso j f.unop.hom
  pushout hi h := ((exactCorestrict j T).map_isPullback h.unop hi).op

/-- Actual target cocylinder data comes from the genuine opposite complex model. -/
def complexOppositeJointData : RowFactorization.JointData
    (NestedWeakEquivalences.refl (complexOppositeWaldhausen j T)) :=
  oppositeComplexJointData (complexObjects j T) (fun _ h => complexObjects_shift j T h (-1))

end Quillen.PerfectComplexes.SupportedOpenDerivedImage
