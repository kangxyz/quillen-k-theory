/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.CategoryTheory.ExactCategory.Resolution.Finite
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Quillen.CategoryTheory.ExactCategory.Subcategory
public import Quillen.Devissage.Filtration
public import Aglib.CategoryTheory.ExactCategory.KernelClosed

/-! # Grothendieck classes of actual finite admissible resolutions -/
@[expose] public section
open CategoryTheory.ExactCategory
noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ExactCategory.ExactStructure.FiniteResolution
open Quillen
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  {E : ExactStructure C} {P : C → Prop}

/-- Resolving an object puts its class in every subgroup containing the classes
of resolving objects. -/
theorem class_mem {X : C} (R : E.FiniteResolution P X)
    (H : AddSubgroup E.GrothendieckGroup)
    (hH : ∀ Y, P Y → E.grothendieckClass Y ∈ H) :
    E.grothendieckClass X ∈ H := by
  induction R with
  | of_mem hX => exact hH _ hX
  | step S hS hP R ih =>
    have h := E.grothendieckClass_additive hS
    have he : E.grothendieckClass S.X₃ =
        E.grothendieckClass S.X₂ - E.grothendieckClass S.X₁ := by rw [h]; abel
    rw [he]
    exact H.sub_mem (hH _ hP) ih

end CategoryTheory.ExactCategory.ExactStructure.FiniteResolution
