/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.KTheory.Map.Functoriality
public import Mathlib.Algebra.Category.Grp.Basic

/-!
# Bundled small exact categories and the Quillen K-group functor

The objects here are exact categories small in a fixed universe, with chosen
additive/zero data. Morphisms are genuine additive conflation-preserving exact
functors. The checked identity/composition laws package K_n as a group-valued
functor, without claiming K₀ commutativity.
-/
@[expose] public section


noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits

namespace Quillen

/-- A small additive category equipped with a genuine Quillen exact structure. -/
structure SmallExactCategory : Type (u + 1) where
  /-- The type of objects of the bundled category, small in the selected universe. -/
  Obj : Type u
  [category : Category.{u} Obj]
  [preadditive : Preadditive Obj]
  [finiteBiproducts : HasFiniteBiproducts Obj]
  /-- The Quillen exact structure on the bundled additive category. -/
  exactStructure : ExactStructure Obj

attribute [instance] SmallExactCategory.category SmallExactCategory.preadditive
  SmallExactCategory.finiteBiproducts

namespace ExactFunctor

/-- The proof data of exactness do not alter equality of exact functors. -/
@[ext]
theorem ext_toFunctor {C D : Type u} [Category.{u} C] [Category.{u} D]
    [Preadditive C] [HasFiniteBiproducts C] [Preadditive D] [HasFiniteBiproducts D]
    {E : ExactStructure C} {E' : ExactStructure D} {F G : ExactFunctor E E'}
    (h : F.toFunctor = G.toFunctor) : F = G := by
  cases F
  cases G
  cases h
  rfl

end ExactFunctor

namespace SmallExactCategory

instance : Category.{u} SmallExactCategory.{u} where
  Hom C D := ExactFunctor C.exactStructure D.exactStructure
  id C := ExactFunctor.id C.exactStructure
  comp F G := F.comp G
  id_comp := by intros; apply ExactFunctor.ext_toFunctor; rfl
  comp_id := by intros; apply ExactFunctor.ext_toFunctor; rfl
  assoc := by intros; apply ExactFunctor.ext_toFunctor; rfl

/-- The actual group-valued Quillen K-functor in a fixed nonnegative degree. -/
def KFunctor (n : ℕ) : SmallExactCategory.{u} ⥤ GrpCat.{u} where
  obj C := GrpCat.of (C.exactStructure.K n)
  map F := GrpCat.ofHom (F.KMap n)
  map_id C := by
    apply ConcreteCategory.hom_ext
    intro x
    exact DFunLike.congr_fun (ExactFunctor.KMap_id C.exactStructure n) x
  map_comp F G := by
    apply ConcreteCategory.hom_ext
    intro x
    exact DFunLike.congr_fun (ExactFunctor.KMap_comp F G n) x

end SmallExactCategory
end Quillen
