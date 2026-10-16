/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.SplitComplexes.MappingConeKZeroRelation
public import Quillen.AlgebraicGeometry.PerfectComplexes.KTheory
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalClosure

/-! Actual perfect mapping cones retain their signed class, without a cofibration assumption. -/
@[expose] public section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open AlgebraicGeometry.Scheme.Modules.Complex
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes
open Quillen.Waldhausen.SplitFactorization
universe u
namespace QuillenTest.MappingConeKZeroRelation

/-- The original perfect mapping cone has the literal target/source class formula. -/
theorem perfect_original_mappingCone_class (X : Scheme.{u}) {K L : Perfect X} (f : K ⟶ L) :
    (perfectWaldhausen X).kZeroObjectClass
        ⟨CochainComplex.mappingCone f.hom,
          locallyPerfect_mappingCone K.property L.property f.hom⟩ =
      (perfectWaldhausen X).kZeroObjectClass L *
        ((perfectWaldhausen X).kZeroObjectClass K)⁻¹ :=
  subcategoryCone_kZeroObjectClass (locallyPerfect X)
    (fun hK hL g => locallyPerfect_mappingCone hK hL g) f

/-- A weak original arrow has a cone with the identity class, even without being a cofibration. -/
private theorem perfect_weak_mappingCone_class (X : Scheme.{u})
    {K L : Perfect X} (f : K ⟶ L) (hf : (perfectWaldhausen X).weq f) :
    (perfectWaldhausen X).kZeroObjectClass
        ⟨CochainComplex.mappingCone f.hom,
          locallyPerfect_mappingCone K.property L.property f.hom⟩ = 1 := by
  rw [perfect_original_mappingCone_class,
    (perfectWaldhausen X).kZeroObjectClass_weak f hf]
  exact mul_inv_cancel _

end QuillenTest.MappingConeKZeroRelation
