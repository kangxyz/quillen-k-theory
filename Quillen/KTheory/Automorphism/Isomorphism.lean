/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.KTheory.Automorphism.Cube

/-!
# Isomorphism invariance of the actual Q automorphism class and cube

Replacing an object by a specified isomorphic object gives an exact
endofunctor naturally isomorphic to the identity. Exact-functor naturality
therefore proves invariance of the existing automorphism class and of its
literal transposed cube. The original R5 proof is retained; no K₁ comparison
or matrix marking is assumed.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open Quillen Quillen.Automorphism Quillen.Automorphism.Functoriality

namespace Quillen.Automorphism.Isomorphism
variable {C : Type u} [SmallCategory C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- Replacing one object by an isomorphic object is an actual exact endofunctor. -/
def replaceExact {A B : C} (e : A ≅ B) : ExactFunctor E E where
  toFunctor := rebaseFunctor (𝟭 C) A B e
  additive := Functor.additive_of_iso (rebaseFunctorIso (𝟭 C) A B e)
  map_conflation S h := by
    let : (rebaseFunctor (𝟭 C) A B e).Additive :=
      Functor.additive_of_iso (rebaseFunctorIso (𝟭 C) A B e)
    exact E.iso_closed (S.mapNatIso (rebaseFunctorIso (𝟭 C) A B e)) h

/-- The actual K-map of this endofunctor is the identity. -/
theorem replaceExact_KMap {A B : C} (e : A ≅ B) (n : ℕ) :
    (replaceExact E e).KMap n = MonoidHom.id (E.K n) := by
  have h : (ExactFunctor.id E).KMap n = (replaceExact E e).KMap n :=
    ExactFunctor.KMap_eq_of_natIso (rebaseFunctorIso (𝟭 C) A B e) n
  rw [← h, ExactFunctor.KMap_id]

/-- Object replacement carries its specified original object to the chosen target. -/
lemma replaceExact_obj {A B : C} (e : A ≅ B) : (replaceExact E e).toFunctor.obj A = B :=
  rebaseFunctor_obj_base _ _ _ _

/-- Its actual automorphism action is conjugation by the given original isomorphism. -/
theorem replaceExact_mapIso {A B : C} (e : A ≅ B) (α : Aut A) :
    Aut.autMulEquivOfIso (eqToIso (replaceExact_obj E e))
      ((replaceExact E e).toFunctor.mapIso α) = Aut.autMulEquivOfIso e α := by
  classical
  apply Iso.ext
  simp [replaceExact, rebaseFunctor, rebaseObjIso, Aut.autMulEquivOfIso]

/-- Equality transport on objects does not change the automorphism class. -/
theorem automorphismClass_eqToIso {A B : C} (h : A = B) (α : Aut A) :
    automorphismClass E B (Aut.autMulEquivOfIso (eqToIso h) α) = automorphismClass E A α := by
  subst B
  have hc : Aut.autMulEquivOfIso (eqToIso (rfl : A = A)) α = α := by
    apply Iso.ext
    simp [Aut.autMulEquivOfIso]
  rw [hc]

/-- A change of coordinates preserves the genuine canonical automorphism class. -/
theorem automorphismClass_conjugate {A B : C} (e : A ≅ B) (α : Aut A) :
    automorphismClass E B (Aut.autMulEquivOfIso e α) = automorphismClass E A α := by
  rw [← replaceExact_mapIso E e α]
  rw [automorphismClass_eqToIso]
  have hn := automorphismClass_natural (replaceExact E e) A α
  rw [replaceExact_KMap] at hn
  exact hn.symm

end Quillen.Automorphism.Isomorphism

namespace Quillen.Automorphism.Isomorphism
variable {C : Type u} [SmallCategory C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- Isomorphic coordinates give the same literal transposed cube class. -/
theorem automorphismFirstCube_class_conjugate {A B : C} (e : A ≅ B) (g : Aut A) :
    (Quotient.mk' (Cube.automorphismFirstCube E B (Aut.autMulEquivOfIso e g)) : E.K 1) =
      Quotient.mk' (Cube.automorphismFirstCube E A g) := by
  rw [Cube.automorphismFirstCube_class, Cube.automorphismFirstCube_class,
    automorphismClass_conjugate]
end Quillen.Automorphism.Isomorphism
