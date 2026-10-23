/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/

module

public import Quillen.Aglib.CategoryTheory.Pi.Abelian
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.Abelian.SerreClass.Exact
public import Aglib.CategoryTheory.Abelian.SerreClass.FiniteProducts
public import Aglib.CategoryTheory.Pi.FiniteSupport

/-! # Exact inclusion of native finite-support families

The native Serre subcategory supplies the abelian structure and coordinate evaluation.
This extension bundles its literal inclusion and records the original evaluation formulas.
-/

@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
attribute [local instance] Abelian.hasFiniteBiproducts
namespace CategoryTheory.Pi
universe u v w
variable {I : Type u} (C : I → Type v) [∀ i, Category.{w} (C i)] [∀ i, Abelian (C i)]

/-- The standard abelian exact structure on the canonical finite-support family. -/
abbrev finiteCategoryExactStructure :=
  ExactCategory.abelianExactStructure (FiniteCategoryFamily C)

/-- The literal full-subcategory inclusion, bundled as an exact functor. -/
def finiteCategoryInclusion : ExactCategory.ExactFunctor (finiteCategoryExactStructure C)
    (ExactCategory.abelianExactStructure (∀ i, C i)) :=
  ObjectProperty.exactInclusion (finiteObjectSupport C)

@[simp]
theorem finiteCategoryEvaluation_obj (i : I) (M : FiniteCategoryFamily C) :
    (finiteCategoryEvaluation C i).toFunctor.obj M = M.obj i := rfl

@[simp]
theorem finiteCategoryEvaluation_map (i : I) {M N : FiniteCategoryFamily C} (f : M ⟶ N) :
    (finiteCategoryEvaluation C i).toFunctor.map f = f.hom i := rfl

end CategoryTheory.Pi
