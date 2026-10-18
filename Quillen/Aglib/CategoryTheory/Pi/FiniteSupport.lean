/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.CategoryTheory.Pi.Abelian
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.Abelian.SerreClass.Exact
public import Aglib.CategoryTheory.Abelian.SerreClass.FiniteProducts
public import Mathlib.Data.Set.Finite.Basic

/-!
# Finite-support families of abelian categories

`finiteObjectSupport C` consists of actual dependent families whose nonzero coordinates form
a finite set, and `FiniteCategoryFamily C` is its full subcategory. This object property is a
Serre class. Its canonical abelian structure and exact inclusion are inherited from the
existing full-subcategory API. `finiteCategoryEvaluation` evaluates the actual coordinate.

This is the canonical migration of `R5Lab.Aglib.CategoryTheory.Pi.FiniteSupport` from R5
revision `1b7c3945394bcc27a94d1ebf86df702b0291ee18`, with the same object predicate and maps.
The former application namespace is replaced by native `CategoryTheory.Pi`; no second family
model is introduced. Its intended upstream module is
`Aglib.CategoryTheory.Pi.FiniteSupport`. Current consumers are the finite-stage comparison
and the finite-support Quillen decomposition. Index, object, and morphism universes remain
independent, including an index in `u` and coordinate categories and homs in `u + 1`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
attribute [local instance] Abelian.hasFiniteBiproducts
namespace CategoryTheory.Pi
universe u v w
variable {I : Type u} (C : I → Type v) [∀ i, Category.{w} (C i)] [∀ i, Abelian (C i)]

/-- Finite nonzero support in a family of actual abelian categories. -/
def finiteObjectSupport : ObjectProperty (∀ i, C i) :=
  fun M => {i | ¬ IsZero (M i)}.Finite

/-- The full subcategory of actual families with finite nonzero support. -/
abbrev FiniteCategoryFamily := (finiteObjectSupport C).FullSubcategory

instance finiteObjectSupport_serre : (finiteObjectSupport C).IsSerreClass where
  exists_zero := by
    obtain ⟨Z, hz⟩ := HasZeroObject.zero (C := ∀ i, C i)
    refine ⟨Z, hz, ?_⟩
    change {i | ¬ IsZero (Z i)}.Finite
    convert Set.finite_empty
    ext i
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
    exact (Pi.eval C i).map_isZero hz
  prop_of_mono f hf h := by
    let := hf
    let : ∀ i, Mono (f i) := fun i => (Pi.eval _ i).map_mono f
    apply h.subset
    intro i hi hz
    exact hi (ObjectProperty.prop_of_mono (IsZero (C := C i)) (f i) hz)
  prop_of_epi f hf h := by
    let := hf
    let : ∀ i, Epi (f i) := fun i => (Pi.eval _ i).map_epi f
    apply h.subset
    intro i hi hz
    exact hi (ObjectProperty.prop_of_epi (IsZero (C := C i)) (f i) hz)
  prop_X₂_of_shortExact h h₁ h₃ := by
    apply (h₁.union h₃).subset
    intro i hi
    by_contra hn
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hn
    exact hi ((h.map_of_exact (Pi.eval C i)).exact.isZero_of_both_isZero hn.1 hn.2)

/-- The standard abelian exact structure on the canonical finite-support family. -/
abbrev finiteCategoryExactStructure :=
  ExactCategory.abelianExactStructure (FiniteCategoryFamily C)

/-- The literal full-subcategory inclusion, bundled as an exact functor. -/
def finiteCategoryInclusion : ExactCategory.ExactFunctor (finiteCategoryExactStructure C)
    (ExactCategory.abelianExactStructure (∀ i, C i)) :=
  ObjectProperty.exactInclusion (finiteObjectSupport C)

/-- Exact evaluation at the actual coordinate of a finite-support family. -/
def finiteCategoryEvaluation (i : I) : ExactCategory.ExactFunctor
    (finiteCategoryExactStructure C) (ExactCategory.abelianExactStructure (C i)) :=
  (finiteCategoryInclusion C).comp (exactEvaluation C i)

@[simp]
theorem finiteCategoryEvaluation_obj (i : I) (M : FiniteCategoryFamily C) :
    (finiteCategoryEvaluation C i).toFunctor.obj M = M.obj i := rfl

@[simp]
theorem finiteCategoryEvaluation_map (i : I) {M N : FiniteCategoryFamily C} (f : M ⟶ N) :
    (finiteCategoryEvaluation C i).toFunctor.map f = f.hom i := rfl

end CategoryTheory.Pi
