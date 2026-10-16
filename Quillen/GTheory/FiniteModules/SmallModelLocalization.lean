/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.Algebra.Category.FGModuleCat.SmallModelLocalization
public import Quillen.CategoryTheory.SmallModel.Exact
public import Aglib.Algebra.Category.FGModuleCat.Localization
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Aglib.Algebra.Category.FGModuleCat.Localization.Quotient
public import Aglib.Algebra.Category.FGModuleCat.Basic
public import Aglib.CategoryTheory.SmallModel.Abelian
public import Mathlib.CategoryTheory.Localization.Equivalence

/-! # Q/K comparison for finite-module small-model localization -/
@[expose] public section
open CategoryTheory.ExactCategory ModuleCat.FiniteLocalization ModuleCat
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.FiniteModuleLocalization
variable {R : Type u} [CommRing R] [IsNoetherianRing R] (S : Submonoid R)

instance smallModelToAbelian_mapQ_isEquivalence (A : Type u) [CommRing A] [IsNoetherianRing A] :
    (smallModelToAbelian A).mapQ.IsEquivalence := by
  apply CategoryTheory.ExactCategory.ExactFunctor.mapQ_isEquivalence_of_equivalence
  · intro M N f hf
    change ((abelianExactStructure (FGModuleCat.{u} A)).smallModel).inflation f
    rw [abelianExactStructure_smallModel]
    exact hf
  · intro M N f hf
    change ((abelianExactStructure (FGModuleCat.{u} A)).smallModel).deflation f
    rw [abelianExactStructure_smallModel]
    exact hf

/-- Canonical identity-induced equivalence between the two proved-equal
small exact structures on finite modules. -/
def smallAbelianKEquiv (A : Type u) [CommRing A] [IsNoetherianRing A] (n : ℕ) :
    (ModuleCat.finiteModuleExactStructure.{u, u} A).SmallK n ≃*
      (abelianExactStructure (SmallModel.{u} (FGModuleCat.{u} A))).K n :=
  (smallModelToAbelian A).KEquivOfMapQIsEquivalence n

/-- Comparison with the standard abelian model preserves exactly the
original localization `smallKMap`, including zero normalization. -/
theorem smallKMap_comparison (n : ℕ) :
    (smallAbelianKEquiv (Localization S) n).toMonoidHom.comp ((exactFunctor S).smallKMap n) =
      ((smallAbelianExactFunctor S).KMap n).comp (smallAbelianKEquiv R n).toMonoidHom := by
  change ((smallModelToAbelian (Localization S)).KMap n).comp
      ((exactFunctor S).smallModel.KMap n) =
    ((smallAbelianExactFunctor S).KMap n).comp ((smallModelToAbelian R).KMap n)
  rw [← CategoryTheory.ExactCategory.ExactFunctor.KMap_comp, ←
    CategoryTheory.ExactCategory.ExactFunctor.KMap_comp]
  rfl

end Quillen.FiniteModuleLocalization
