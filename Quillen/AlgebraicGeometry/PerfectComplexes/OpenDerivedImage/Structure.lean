/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenDerivedImage.Closure
public import Quillen.AlgebraicGeometry.PerfectComplexes.OppositeJointData

/-! # Actual Waldhausen structures on the derived-saturated image

The image is an extension-closed full subcategory of actual complexes. Its
cofibrations are proved to be precisely inherited perfect cofibrations by
constructing the genuine quotient membership. The opposite structure uses
actual admissible epis and kernels. The roof hypothesis is explicit.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex Opposite
open scoped ZeroObject
universe u
namespace Quillen.PerfectComplexes.OpenDerivedImage
open Waldhausen Fibration
attribute [local instance] HasDerivedCategory.standard Abelian.hasFiniteBiproducts
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

instance complexObjects_closedUnderIsomorphisms : (complexObjects j).IsClosedUnderIsomorphisms where
  of_iso e h := (complexObjects_iff_of_derivedIso j ((toDerived U).mapIso e)).mp h

instance complexObjects_containsZero : (complexObjects j).ContainsZero where
  exists_zero := ⟨0, isZero_zero _,
    (derivedObjects j).prop_of_isZero ((toDerived U).map_isZero (isZero_zero _))⟩

/-- The original shifted complex stays in the actual derived image. -/
theorem complexObjects_shift {E : Complex U} (hE : complexObjects j E) (n : ℤ) :
    complexObjects j (E⟦n⟧) := by
  have h : derivedObjects j (((toDerived U).obj E)⟦n⟧) := (derivedObjects j).le_shift _ _ hE
  exact (derivedObjects j).prop_of_iso (((toDerived U).commShiftIso n).app E).symm h

variable [Fact (HasDerivedRoofs j)]

instance complexObjects_extensionClosed :
    (abelianExactStructure (Complex U)).IsExtensionClosed (complexObjects j) where
  prop_middle := complexObjects_of_shortExact j (Fact.out : HasDerivedRoofs j)

instance complexObjects_closedUnderFiniteProducts : (complexObjects j).IsClosedUnderFiniteProducts
  :=
  (abelianExactStructure (Complex U)).extensionClosed_finiteProducts (complexObjects j)

/-- The actual full subcategory with one underlying chain-complex wrapper. -/
abbrev ComplexObj := (complexObjects j).FullSubcategory

/-- Genuine original quasi-isomorphisms and inherited admissible monomorphisms. -/
def complexWaldhausen : Structure (ComplexObj j) := complexSubcategory (complexObjects j)

/-- Original admissible epimorphisms on the literal opposite. -/
def complexOppositeWaldhausen : Structure (ComplexObj j)ᵒᵖ := oppositeComplexSubcategory
  (complexObjects j)

theorem complexOpposite_compatible : IsCompatibleDual (complexWaldhausen j)
  (complexOppositeWaldhausen j) :=
  oppositeComplexSubcategory_compatible (complexObjects j)

/-- Actual image inclusion into original perfect complexes. -/
def inclusion : ComplexObj j ⥤ Perfect U := ObjectProperty.ιOfLE (fun _ h => locallyPerfect_of_mem j
  h)

theorem inclusion_exact : IsExact (complexWaldhausen j).cof (complexWaldhausen j).weq
    (perfectWaldhausen U).cof (perfectWaldhausen U).weq (inclusion j) :=
  subcategoryInclusion_exact (complexObjects j) (locallyPerfect U) (fun _ h => locallyPerfect_of_mem
    j h)

/-- Reflection retains the actual ambient perfect quotient and proves that
same quotient belongs to the derived image. -/
theorem inclusion_cof_iff {A B : ComplexObj j} (f : A ⟶ B) :
    (perfectWaldhausen U).cof ((inclusion j).map f) ↔ (complexWaldhausen j).cof f := by
  constructor
  · intro hf
    obtain ⟨Z, hZ, p, hp, hS⟩ := (ExactSubcategory.inflation_iff (abelianExactStructure (Complex U))
      (locallyPerfect U) ((inclusion j).map f)).mp hf
    apply (ExactSubcategory.inflation_iff (abelianExactStructure (Complex U)) (complexObjects j)
      f).mpr
    exact ⟨Z, complexObjects_quotient_of_shortExact j (Fact.out : HasDerivedRoofs j)
      hS A.property B.property, p, hp, hS⟩
  · exact (inclusion_exact j).cofibration f

/-- The original restriction functor with its literal image witness. -/
def complexCorestrict : Perfect X ⥤ ComplexObj j :=
  (complexObjects j).lift ((locallyPerfect X).ι ⋙ restrict j)
    (fun A => ⟨A.obj, A.property, ⟨Iso.refl _⟩⟩)

instance complexCorestrict_additive : (complexCorestrict j).Additive := by
  unfold complexCorestrict
  infer_instance

/-- The genuine actual exact-subcategory restriction functor. -/
def exactCorestrict : Quillen.ExactFunctor (ExactSubcategory.exactStructure (abelianExactStructure
  (Complex X)) (locallyPerfect X))
    (ExactSubcategory.exactStructure (abelianExactStructure (Complex U)) (complexObjects j)) where
  toFunctor := complexCorestrict j
  map_conflation S hS := by
    change ((S.map (locallyPerfect X).ι).map (restrict j)).ShortExact
    exact hS.map_of_exact _

/-- Original restriction is genuinely exact on the saturated image. -/
theorem complexCorestrict_exact : IsExact (perfectWaldhausen X).cof (perfectWaldhausen X).weq
    (complexWaldhausen j).cof (complexWaldhausen j).weq (complexCorestrict j) where
  zero h := (complexCorestrict j).map_isZero h
  cofibration f hf := (exactCorestrict j).map_inflation f hf
  weak f hf := by
    have : QuasiIso f.hom := hf
    exact restrict_quasiIso j f.hom
  pushout hi h := by
    apply IsPushout.of_map_of_faithful (complexObjects j).ι
    exact (fullSubcategory_map_pushout (abelianExactStructure (Complex X))
      (locallyPerfect X) hi h).map (restrict j)

/-- The unchanged restriction is exact on the actual opposite structures. -/
theorem complexCorestrict_op_exact : IsExact
    (perfectOppositeWaldhausen X).cof (perfectOppositeWaldhausen X).weq
    (complexOppositeWaldhausen j).cof (complexOppositeWaldhausen j).weq (complexCorestrict j).op
      where
  zero h := (complexCorestrict j).op.map_isZero h
  cofibration f hf := (exactCorestrict j).map_deflation f.unop hf
  weak f hf := by
    have : QuasiIso f.unop.hom := hf
    exact restrict_quasiIso j f.unop.hom
  pushout hi h := ((exactCorestrict j).map_isPullback h.unop hi).op

/-- Actual target cocylinder data comes from the genuine opposite complex model. -/
def complexOppositeJointData : RowFactorization.JointData
    (NestedWeakEquivalences.refl (complexOppositeWaldhausen j)) :=
  oppositeComplexJointData (complexObjects j) (fun _ h => complexObjects_shift j h (-1))

end Quillen.PerfectComplexes.OpenDerivedImage
