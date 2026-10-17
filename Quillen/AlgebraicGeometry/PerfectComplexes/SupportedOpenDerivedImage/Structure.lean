/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.SupportedOpenDerivedImage.Exact
public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOppositeJointData


public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.SupportedOpenDerivedImage.Closure
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
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

open Quillen.Waldhausen


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
open Waldhausen Fibration
attribute [local instance] HasDerivedCategory.standard Abelian.hasFiniteBiproducts
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

variable [Fact (OpenDerivedImage.HasSupportedDerivedRoofs j T)]

/-- Genuine original quasi-isomorphisms and inherited admissible monomorphisms. -/
def complexWaldhausen : Structure (ComplexObj j T) := complexSubcategory (complexObjects j T)

/-- Original admissible epimorphisms on the literal opposite. -/
def complexOppositeWaldhausen : Structure (ComplexObj j T)ᵒᵖ := oppositeComplexSubcategory
  (complexObjects j T)

theorem complexOpposite_compatible : IsCompatibleDual (complexWaldhausen j T)
  (complexOppositeWaldhausen j T) :=
  oppositeComplexSubcategory_compatible (complexObjects j T)

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
    obtain ⟨Z, hZ, p, hp, hS⟩ := (ExactSubcategory.inflation_iff
      (abelianExactStructure (CochainComplex U.Modules ℤ))
      (perfectSupported (j ⁻¹ᵁ T).ι) ((inclusion j T).map f)).mp hf
    apply (ExactSubcategory.inflation_iff (abelianExactStructure (CochainComplex U.Modules ℤ))
      (complexObjects j T)
      f).mpr
    exact ⟨Z, complexObjects_quotient_of_shortExact j T (Fact.out :
      OpenDerivedImage.HasSupportedDerivedRoofs j T)
      hS A.property B.property, p, hp, hS⟩
  · exact (inclusion_exact j T).cofibration f

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
    exact (fullSubcategory_map_pushout (abelianExactStructure (CochainComplex X.Modules ℤ))
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
