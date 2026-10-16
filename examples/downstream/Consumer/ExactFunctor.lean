/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Basic
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Quillen.KTheory.API

/-!
# Exact functor K-theory examples

Bundles supplied exact structures and uses the public K-theory maps for exact
functors. The statements record identity and composition, agreement with the
bundled K-functor, the forward map of an equivalence induced on Q-constructions,
and equality for naturally isomorphic functors.
-/

@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits

namespace Consumer
variable {C D T : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} T]
  [Preadditive C] [HasFiniteBiproducts C] [Preadditive D] [HasFiniteBiproducts D]
  [Preadditive T] [HasFiniteBiproducts T]
  (E : ExactStructure C) (E' : ExactStructure D) (E'' : ExactStructure T)

/-- Bundle the supplied small category with its original selected exact structure. -/
def bundled : SmallExactCategory.{u} :=
  SmallExactCategory.ofExactStructure E

/-- The existing group structure on the genuine K-group. -/
abbrev kGroupInstance (n : ℕ) : Group (E.K n) := inferInstance
theorem identity_map (n : ℕ) (x : E.K n) : (CategoryTheory.ExactCategory.ExactFunctor.id E).KMap n x
  = x := by simp

theorem composition_map (F : ExactFunctor E E') (G : ExactFunctor E' E'') (n : ℕ) (x : E.K n) :
    (F.comp G).KMap n x = G.KMap n (F.KMap n x) := by simp

theorem bundled_functor_map (F : ExactFunctor E E') (n : ℕ) (x : E.K n) :
    (SmallExactCategory.KFunctor n).map
      (show bundled E ⟶ bundled E' from F) x = F.KMap n x := rfl

-- The public equivalence keeps the original canonical forward homomorphism.
theorem equivalence_forward_map (F : ExactFunctor E E') [F.mapQ.IsEquivalence] (n : ℕ) :
    (F.KEquivOfMapQIsEquivalence n).toMonoidHom = F.KMap n :=
  F.KEquivOfMapQIsEquivalence_coe n

theorem naturally_isomorphic_maps (F G : ExactFunctor E E')
    (e : F.toFunctor ≅ G.toFunctor) (n : ℕ) : F.KMap n = G.KMap n :=
  CategoryTheory.ExactCategory.ExactFunctor.KMap_eq_of_natIso e n
end Consumer
