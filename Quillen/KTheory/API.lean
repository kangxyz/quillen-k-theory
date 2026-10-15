/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Basic
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Quillen.KTheory.Functor
public import Quillen.KTheory.Equivalence
public import Quillen.KTheory.Map.CommonAmbient
public import Aglib.CategoryTheory.SmallModel.Abelian
public import Quillen.CategoryTheory.SmallModel.Functoriality

/-!
# Public exact-category K-theory interface

Use `E.K n` for an exact structure, `F.KMap n` for an exact functor, and
`E.SmallK n` / `F.smallKMap n` when passing to an essentially small model.
`SmallExactCategory.ofExactStructure` packages an existing small exact category
for the group-valued `SmallExactCategory.KFunctor` without new mathematical data.
-/
@[expose] public section

open CategoryTheory.ExactCategory



noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits

namespace Quillen.SmallExactCategory

/-- Bundle an existing small exact category for the group-valued K-functor. -/
def ofExactStructure {C : Type u} [Category.{u} C] [Preadditive C]
    [HasFiniteBiproducts C] (E : ExactStructure C) : SmallExactCategory.{u} where
  Obj := C
  exactStructure := E

/-- The K-groups of a bundled small exact category. -/
abbrev K (C : SmallExactCategory.{u}) (n : ℕ) := C.exactStructure.K n

/-- Bundling does not change the original K-group. -/
@[simp] theorem ofExactStructure_K {C : Type u} [Category.{u} C] [Preadditive C]
    [HasFiniteBiproducts C] (E : ExactStructure C) (n : ℕ) :
    (ofExactStructure E).K n = E.K n := rfl

/-- The group-valued functor evaluates to the same genuine K-group. -/
@[simp] theorem KFunctor_obj (C : SmallExactCategory.{u}) (n : ℕ) :
    (KFunctor n).obj C = GrpCat.of (C.K n) := rfl

/-- The bundled functor uses precisely the canonical exact-functor K-map. -/
@[simp] theorem KFunctor_map_hom {C D : SmallExactCategory.{u}} (F : C ⟶ D) (n : ℕ) :
    GrpCat.Hom.hom (X := GrpCat.of (C.K n)) (Y := GrpCat.of (D.K n))
      ((KFunctor n).map F) = F.KMap n := rfl


end Quillen.SmallExactCategory

namespace CategoryTheory.ExactCategory.ExactFunctor
open Quillen

variable {C D T : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} T]
  [Preadditive C] [HasFiniteBiproducts C] [Preadditive D] [HasFiniteBiproducts D]
  [Preadditive T] [HasFiniteBiproducts T]
  {EC : ExactStructure C} {ED : ExactStructure D} {ET : ExactStructure T}

/-- Pointwise identity law for the canonical K-map. -/
theorem KMap_id_apply (E : ExactStructure C) (n : ℕ) (x : E.K n) :
    (CategoryTheory.ExactCategory.ExactFunctor.id E).KMap n x = x := by
  rw [KMap_id]
  rfl

/-- Pointwise composition law, convenient in downstream calculations. -/
theorem KMap_comp_apply (F : ExactFunctor EC ED) (G : ExactFunctor ED ET)
    (n : ℕ) (x : EC.K n) :
    (F.comp G).KMap n x = G.KMap n (F.KMap n x) := by
  rw [KMap_comp]
  rfl

end CategoryTheory.ExactCategory.ExactFunctor
