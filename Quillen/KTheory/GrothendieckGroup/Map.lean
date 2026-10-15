/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.KTheory.GrothendieckGroup.Basic
public import Quillen.CategoryTheory.ExactCategory.Functor

/-! # Exact-functor maps on algebraic Grothendieck groups

These are algebraic Grothendieck groups. Their comparison with the homotopical
K₀ remains a separate theorem.
-/
@[expose] public section


noncomputable section
universe v₁ v₂ v₃ u₁ u₂ u₃
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ExactCategory.ExactFunctor
open Quillen
variable {C : Type u₁} {D : Type u₂} {B : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} B]
  [Preadditive C] [HasFiniteBiproducts C]
  [Preadditive D] [HasFiniteBiproducts D]
  [Preadditive B] [HasFiniteBiproducts B]
  {EC : CategoryTheory.ExactCategory.ExactStructure C} {ED :
    CategoryTheory.ExactCategory.ExactStructure D}
  {EB : CategoryTheory.ExactCategory.ExactStructure B}

/-- Exact functors send the defining conflation relations to relations. -/
def grothendieckMap (F : ExactFunctor EC ED) : EC.GrothendieckGroup →+ ED.GrothendieckGroup :=
  EC.grothendieckLift (fun X => ED.grothendieckClass (F.toFunctor.obj X))
    (fun S hS => ED.grothendieckClass_additive (F.map_conflation S hS))

@[simp]
lemma grothendieckMap_class (F : ExactFunctor EC ED) (X : C) :
    F.grothendieckMap (EC.grothendieckClass X) =
      ED.grothendieckClass (F.toFunctor.obj X) :=
  EC.grothendieckLift_class _ _ X

@[simp]
lemma grothendieckMap_id :
    (CategoryTheory.ExactCategory.ExactFunctor.id EC).grothendieckMap = AddMonoidHom.id
      EC.GrothendieckGroup := by
  apply EC.grothendieck_hom_ext
  intro X
  simp [CategoryTheory.ExactCategory.ExactFunctor.id]

@[simp]
lemma grothendieckMap_comp (F : ExactFunctor EC ED) (G : ExactFunctor ED EB) :
    (F.comp G).grothendieckMap = G.grothendieckMap.comp F.grothendieckMap := by
  apply EC.grothendieck_hom_ext
  intro X
  simp [CategoryTheory.ExactCategory.ExactFunctor.comp]

end CategoryTheory.ExactCategory.ExactFunctor
