/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.GrothendieckComparison.Equivalence
public import Quillen.KTheory.Functor

/-!
# The natural isomorphism from classical Grothendieck groups to Quillen K₀

For bundled small exact categories, the original object/conflation
Grothendieck groups form a group-valued functor. The canonical comparison is
an actual natural isomorphism to the existing homotopical `KFunctor 0`.
-/
@[expose] public section

noncomputable section
universe u
open CategoryTheory
namespace CategoryTheory.ExactCategory.SmallExactCategory

/-- The classical object/conflation Grothendieck group functor, written
multiplicatively to compare with the existing group-valued K-functor. -/
def grothendieckFunctor : SmallExactCategory.{u} ⥤ GrpCat.{u} where
  obj C := GrpCat.of (Multiplicative C.exactStructure.GrothendieckGroup)
  map F := GrpCat.ofHom F.grothendieckMap.toMultiplicative
  map_id C := by
    apply ConcreteCategory.hom_ext
    intro a
    change (CategoryTheory.ExactCategory.ExactFunctor.id
      C.exactStructure).grothendieckMap.toMultiplicative a = a
    rw [CategoryTheory.ExactCategory.ExactFunctor.grothendieckMap_id]
    rfl
  map_comp F G := by
    apply ConcreteCategory.hom_ext
    intro a
    change (F.comp G).grothendieckMap.toMultiplicative a =
      G.grothendieckMap.toMultiplicative (F.grothendieckMap.toMultiplicative a)
    rw [CategoryTheory.ExactCategory.ExactFunctor.grothendieckMap_comp]
    rfl

/-- The original canonical object-class comparison is a natural isomorphism
from the classical Grothendieck presentation to genuine homotopical Quillen K₀. -/
def grothendieckKZeroIso : grothendieckFunctor.{u} ≅ KFunctor 0 :=
  NatIso.ofComponents (fun C ↦ C.exactStructure.grothendieckKZeroEquiv.toGrpIso) (by
    intro C D F
    apply ConcreteCategory.hom_ext
    intro a
    exact (DFunLike.congr_fun F.grothendieckToKZero_naturality a).symm)

/-- The forward component is exactly the original canonical comparison. -/
@[simp] theorem grothendieckKZeroIso_hom_app (C : SmallExactCategory.{u}) :
    grothendieckKZeroIso.hom.app C = GrpCat.ofHom C.exactStructure.grothendieckToKZero := rfl

/-- The inverse component is exactly the genuine topological retraction. -/
@[simp] theorem grothendieckKZeroIso_inv_app (C : SmallExactCategory.{u}) :
    grothendieckKZeroIso.inv.app C = GrpCat.ofHom C.exactStructure.kZeroToGrothendieck := rfl

end CategoryTheory.ExactCategory.SmallExactCategory
