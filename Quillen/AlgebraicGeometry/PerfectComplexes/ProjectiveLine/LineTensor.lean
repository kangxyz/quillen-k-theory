/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.TensorByLine


public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Aglib.AlgebraicGeometry.Modules.Complex.Tensor
public import Quillen.AlgebraicGeometry.PerfectComplexes.FlatPullback
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalDescent
public import Aglib.AlgebraicGeometry.Cohomology.ProjectionFormula.TensorPushforward
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Tensor.Exact
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.Complex.Restriction
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Restriction
/-! # Exact tensor with an actually trivialized line on locally perfect complexes

Degreewise tensor uses the original sheafified tensor functor. Actual line
trivializations identify its open restrictions with the original restrictions.
This proves preservation of the local perfect predicate, with no global strict
representative and no derived tensor product of two arbitrary complexes.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open Quillen



open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes
open AlgebraicGeometry.Scheme.Modules
open CategoryTheory.MonoidalCategory

variable {X : Scheme.{u}} (L : X.Modules) {ι : Type v}
  (Y : ι → Scheme.{u}) (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)]
  (hc : ∀ x : X, ∃ i y, j i y = x)
  (e : ∀ i, L.restrict (j i) ≅ SheafOfModules.unit (Y i).ringCatSheaf)

include hc e

variable [IsFiniteLocallyFree X L]

/-- The original perfect Waldhausen structure sees actual line tensor as exact. -/
theorem perfectTensorByLine_waldhausenExact :
    Waldhausen.IsExact (perfectWaldhausen X).cof (perfectWaldhausen X).weq
      (perfectWaldhausen X).cof (perfectWaldhausen X).weq (perfectTensorByLine L Y j hc e) where
  zero h := (perfectTensorByLine L Y j hc e).map_isZero h
  cofibration s hs := (perfectExactTensorByLine L Y j hc e).map_inflation s hs
  weak s hs := by
    let : QuasiIso s.hom := hs
    exact AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft_quasiIso L s.hom
  pushout hi h := by
    apply IsPushout.of_map_of_faithful (locallyPerfect X).ι
    exact (Waldhausen.fullSubcategory_map_pushout (abelianExactStructure
      (CochainComplex X.Modules ℤ))
      (locallyPerfect X) hi h).map (AlgebraicGeometry.Scheme.Modules.Complex.tensorLeft L)

end Quillen.PerfectComplexes
