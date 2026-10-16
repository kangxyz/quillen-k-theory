/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.OpenDerivedImage.Exact


public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.OpenDerivedImage.Closure
public import Quillen.AlgebraicGeometry.PerfectComplexes.OppositeJointData
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
/-! # Actual Waldhausen structures on the derived-saturated image

The image is an extension-closed full subcategory of actual complexes. Its
cofibrations are proved to be precisely inherited perfect cofibrations by
constructing the genuine quotient membership. The opposite structure uses
actual admissible epis and kernels. The roof hypothesis is explicit.
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
namespace Quillen.PerfectComplexes.OpenDerivedImage
open Waldhausen Fibration
attribute [local instance] HasDerivedCategory.standard Abelian.hasFiniteBiproducts
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

variable [Fact (HasDerivedRoofs j)]

/-- Genuine original quasi-isomorphisms and inherited admissible monomorphisms. -/
def complexWaldhausen : Structure (ComplexObj j) := complexSubcategory (complexObjects j)

/-- Original admissible epimorphisms on the literal opposite. -/
def complexOppositeWaldhausen : Structure (ComplexObj j)ᵒᵖ := oppositeComplexSubcategory
  (complexObjects j)

theorem complexOpposite_compatible : IsCompatibleDual (complexWaldhausen j)
  (complexOppositeWaldhausen j) :=
  oppositeComplexSubcategory_compatible (complexObjects j)

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
    obtain ⟨Z, hZ, p, hp, hS⟩ := (ExactSubcategory.inflation_iff
      (abelianExactStructure (CochainComplex U.Modules ℤ))
      (locallyPerfect U) ((inclusion j).map f)).mp hf
    apply (ExactSubcategory.inflation_iff (abelianExactStructure (CochainComplex U.Modules ℤ))
      (complexObjects j)
      f).mpr
    exact ⟨Z, complexObjects_quotient_of_shortExact j (Fact.out : HasDerivedRoofs j)
      hS A.property B.property, p, hp, hS⟩
  · exact (inclusion_exact j).cofibration f

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
    exact (fullSubcategory_map_pushout (abelianExactStructure (CochainComplex X.Modules ℤ))
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
