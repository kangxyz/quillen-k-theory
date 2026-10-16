/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.Abelian.Subcategory.Exact
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.Devissage.Filtration
public import Quillen.Aglib.CategoryTheory.ExactCategory.Filtration.Hypothesis
public import Quillen.KTheory.Map.Basic
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
# The exact inclusion in classical Quillen dévissage

Let `C` be abelian and let `P` be a property of its objects which contains zero
and is closed under subobjects, quotients, and finite products. The full
subcategory on `P` is genuinely abelian: its kernels and cokernels are created
by the inclusion. The inclusion is exact and therefore induces the actual
Q-construction functor and maps on Quillen K-groups.

The finite-filtration hypothesis says that every ambient object has an actual
finite admissible filtration whose successive quotients satisfy `P`. It implies
surjectivity of the inclusion on the algebraic Grothendieck groups.

There is deliberately no extension-closure hypothesis on `P`. Classical
Quillen dévissage allows the ambient category to contain nontrivial extensions
of objects of the smaller category. A homotopy equivalence and a comparison with homotopical `K₀`
  remain separate
theorems. Algebraic Grothendieck-group injectivity is proved in the subsequent
`Quillen.DevissageGrothendieck` module.
-/
@[expose] public section

open CategoryTheory.ExactCategory
open CategoryTheory.ObjectProperty

open Quillen






noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace Quillen.Devissage

attribute [local instance] Abelian.hasFiniteBiproducts

variable {C : Type u} [Category.{v} C] [Abelian C] (P : ObjectProperty C)

variable [P.ContainsZero] [P.IsClosedUnderSubobjects] [P.IsClosedUnderQuotients]
  [P.IsClosedUnderFiniteProducts]

/-- The Q-functor induced by the exact inclusion in classical dévissage. -/
def mapQ :
    Q (subcategoryExactStructure P).deflation (subcategoryExactStructure P).inflation ⥤
      Q (abelianExactStructure C).deflation (abelianExactStructure C).inflation :=
  (exactInclusion P).mapQ

@[simp]
lemma mapQ_obj_of (X : Subcategory P) :
    (mapQ P).obj
      (Q.of (subcategoryExactStructure P).deflation
        (subcategoryExactStructure P).inflation X) =
    Q.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation X.obj := rfl

/-- The homomorphism on the genuine zero-based Quillen K-groups. This definition
by itself does not assert that the homomorphism is an isomorphism. -/
def KMap (n : ℕ) :
    (subcategoryExactStructure P).K n →* (abelianExactStructure C).K n :=
  (exactInclusion P).KMap n

/-- The inclusion-induced map of algebraic Grothendieck groups. -/
def grothendieckMap :
    (subcategoryExactStructure P).GrothendieckGroup →+
      (abelianExactStructure C).GrothendieckGroup :=
  (exactInclusion P).grothendieckMap

@[simp]
lemma grothendieckMap_class (X : Subcategory P) :
    grothendieckMap P ((subcategoryExactStructure P).grothendieckClass X) =
      (abelianExactStructure C).grothendieckClass X.obj :=
  (exactInclusion P).grothendieckMap_class X

/-- A finite filtration with factors in `P` puts the ambient object's class in
the image of the inclusion-induced algebraic Grothendieck-group map. -/
theorem class_mem_range {X : C} (F : (abelianExactStructure C).Filtration P X) :
    (abelianExactStructure C).grothendieckClass X ∈ (grothendieckMap P).range := by
  apply F.class_mem
  intro Y hY
  exact ⟨(subcategoryExactStructure P).grothendieckClass ⟨Y, hY⟩,
    grothendieckMap_class P ⟨Y, hY⟩⟩

/-- The filtration hypothesis proves surjectivity on algebraic Grothendieck
groups. This is not the homotopical dévissage theorem or the `K₀` comparison. -/
theorem grothendieckMap_surjective (h : FiltrationHypothesis P) :
    Function.Surjective (grothendieckMap P) := by
  apply AddMonoidHom.range_eq_top.mp
  apply CategoryTheory.ExactCategory.ExactStructure.grothendieckSubgroup_eq_top_of_classes
  intro X
  obtain ⟨F⟩ := h X
  exact class_mem_range P F

end Quillen.Devissage
