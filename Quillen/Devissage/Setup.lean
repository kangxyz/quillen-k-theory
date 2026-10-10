/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.CategoryTheory.ExactCategory.Abelian
public import Quillen.Devissage.Filtration
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


noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace Quillen.Devissage

attribute [local instance] Abelian.hasFiniteBiproducts

variable {C : Type u} [Category.{v} C] [Abelian C] (P : ObjectProperty C)

/-- Under subobject closure, the usual nonemptiness requirement is equivalent
to containing a zero object. -/
theorem containsZero_iff_nonempty [P.IsClosedUnderSubobjects] :
    P.ContainsZero ↔ P.Nonempty := by
  constructor
  · intro h
    let := h
    infer_instance
  · intro h
    let := h
    exact ⟨⟨0, isZero_zero C,
      P.prop_of_mono (0 : (0 : C) ⟶ P.arbitrary) P.prop_arbitrary⟩⟩

variable [P.ContainsZero] [P.IsClosedUnderSubobjects] [P.IsClosedUnderQuotients]
  [P.IsClosedUnderFiniteProducts]

/-- The full subcategory of objects allowed as dévissage factors. -/
abbrev Subcategory := P.FullSubcategory

/-- The abelian structure is constructed from the closure hypotheses, rather
than supplied as extra data. -/
@[instance_reducible]
def subcategoryAbelian : Abelian (Subcategory P) := inferInstance

/-- The standard exact structure on the full abelian subcategory. -/
def subcategoryExactStructure : ExactStructure (Subcategory P) :=
  abelianExactStructure (Subcategory P)

/-- The full-subcategory inclusion preserves finite limits because it creates
kernels. -/
theorem inclusion_preservesFiniteLimits : PreservesFiniteLimits P.ι := by
  let : ∀ {X Y : P.FullSubcategory} (f : X ⟶ Y),
      PreservesLimit (parallelPair f 0) P.ι := fun f => P.preservesKernels_ι f
  exact Functor.preservesFiniteLimits_of_preservesKernels P.ι

/-- The full-subcategory inclusion preserves finite colimits because it creates
cokernels. -/
theorem inclusion_preservesFiniteColimits : PreservesFiniteColimits P.ι := by
  let : ∀ {X Y : P.FullSubcategory} (f : X ⟶ Y),
      PreservesColimit (parallelPair f 0) P.ι := fun f => P.preservesCokernels_ι f
  exact Functor.preservesFiniteColimits_of_preservesCokernels P.ι

/-- The actual inclusion is exact for the standard abelian exact structures. -/
def exactInclusion :
    ExactFunctor (subcategoryExactStructure P) (abelianExactStructure C) where
  toFunctor := P.ι
  map_conflation S hS := by
    let := inclusion_preservesFiniteLimits P
    let := inclusion_preservesFiniteColimits P
    exact hS.map_of_exact P.ι

/-- The exact inclusion remains the ordinary fully faithful inclusion on its
underlying category. This does not assert fullness of the induced Q-functor. -/
def inclusionFullyFaithful : (exactInclusion P).toFunctor.FullyFaithful :=
  P.fullyFaithfulι

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

/-- Classical dévissage requires finite filtrations by actual short exact
sequences, starting with a zero object, and with successive quotients in `P`.
No extension closure is required of `P`. -/
def FiltrationHypothesis : Prop :=
  ∀ X : C, Nonempty ((abelianExactStructure C).Filtration P X)

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
  apply ExactStructure.grothendieckSubgroup_eq_top_of_classes
  intro X
  obtain ⟨F⟩ := h X
  exact class_mem_range P F

end Quillen.Devissage
