/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Basic
public import Aglib.CategoryTheory.ExactCategory.Small
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

open CategoryTheory.ExactCategory

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ExactCategory.SmallExactCategory

/-- The actual group-valued Quillen K-functor in a fixed nonnegative degree. -/
def KFunctor (n : ℕ) : SmallExactCategory.{u} ⥤ GrpCat.{u} where
  obj C := GrpCat.of (C.exactStructure.K n)
  map F := GrpCat.ofHom (F.KMap n)
  map_id C := by
    apply ConcreteCategory.hom_ext
    intro x
    exact DFunLike.congr_fun (CategoryTheory.ExactCategory.ExactFunctor.KMap_id C.exactStructure n)
      x
  map_comp F G := by
    apply ConcreteCategory.hom_ext
    intro x
    exact DFunLike.congr_fun (CategoryTheory.ExactCategory.ExactFunctor.KMap_comp F G n) x

end CategoryTheory.ExactCategory.SmallExactCategory
