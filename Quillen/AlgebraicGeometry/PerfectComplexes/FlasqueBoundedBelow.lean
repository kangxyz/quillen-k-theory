/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.FlasqueBoundedBelow.Basic


public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedBelowComparison
public import Aglib.AlgebraicGeometry.Cohomology.Flasque.Extensions
public import Aglib.AlgebraicGeometry.Cohomology.Godement.TotalComplex.Exactness
public import Aglib.AlgebraicGeometry.Cohomology.Godement.TotalComplex.QuasiIso

/-!
# The original lower-bounded flasque perfect model

This is the full subcategory of original locally perfect complexes of all module
sheaves that have a strict lower bound and flasque terms. The literal Godement
totalization lands in this subcategory and is Waldhausen-exact. Its original
augmentation supplies forward weak natural units on both original models.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Godement
open scoped ZeroObject
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes.FlasqueBoundedBelow

/-- The genuine full Waldhausen subcategory with inherited cofibrations and quasi-isomorphisms. -/
def waldhausen (X : Scheme.{u}) : Waldhausen.Structure (Obj X) :=
  Waldhausen.complexSubcategory (objects X)

/-- The original inclusion is Waldhausen-exact. -/
lemma inclusion_exact (X : Scheme.{u}) : Waldhausen.IsExact
    (waldhausen X).cof (waldhausen X).weq
    (BoundedBelow.waldhausen X).cof (BoundedBelow.waldhausen X).weq (inclusion X) :=
  Waldhausen.subcategoryInclusion_exact _ _ (fun _ h => h.1)

/-- The original quotient-bearing cofibrations are preserved by actual exact totalization. -/
lemma total_cofibration {X : Scheme.{u}} {K L : BoundedBelow.Obj X} (f : K ⟶ L)
    (hf : (BoundedBelow.waldhausen X).cof f) : (waldhausen X).cof ((total X).map f) :=
  (totalExactFunctor X).map_inflation f hf

/-- Original weak arrows are preserved by the actual augmentation and two-out-of-three. -/
lemma total_weak {X : Scheme.{u}} {K L : BoundedBelow.Obj X} (f : K ⟶ L)
    (hf : (BoundedBelow.waldhausen X).weq f) : (waldhausen X).weq ((total X).map f) := by
  change QuasiIso f.hom at hf
  let fplus : (⟨K.obj, K.property.2⟩ : CochainComplex.Plus X.Modules) ⟶
    ⟨L.obj, L.property.2⟩ := ObjectProperty.homMk f.hom
  let : QuasiIso fplus.hom := hf
  change QuasiIso ((godementTotal X).map f.hom)
  exact godementTotalPlus_map_quasiIso fplus

/-- Actual totalization preserves zero, cofibrations, weak arrows, and their pushouts. -/
lemma total_exact (X : Scheme.{u}) : Waldhausen.IsExact
    (BoundedBelow.waldhausen X).cof (BoundedBelow.waldhausen X).weq
    (waldhausen X).cof (waldhausen X).weq (total X) where
  zero h := (total X).map_isZero h
  cofibration f hf := total_cofibration f hf
  weak f hf := total_weak f hf
  pushout hi h := by
    exact (totalExactFunctor X).map_isPushout hi h

/-- Every component of the actual source unit is an original weak equivalence. -/
lemma unit_weak (X : Scheme.{u}) (K : BoundedBelow.Obj X) :
    (BoundedBelow.waldhausen X).weq ((unit X).app K) :=
  godementTotalUnit_quasiIso X ⟨K.obj, K.property.2⟩

/-- Every component of the actual flasque-source unit is an original weak equivalence. -/
lemma flasqueUnit_weak (X : Scheme.{u}) (K : Obj X) :
    (waldhausen X).weq ((flasqueUnit X).app K) :=
  godementTotalUnit_quasiIso X ⟨K.obj, K.property.1.2⟩

end Quillen.PerfectComplexes.FlasqueBoundedBelow

namespace Quillen.PerfectComplexes

end Quillen.PerfectComplexes
