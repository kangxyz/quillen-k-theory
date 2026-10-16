/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.Abelian.Subcategory.Exact
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.Aglib.CategoryTheory.ExactCategory.Filtration.Hypothesis
public import Mathlib.CategoryTheory.Abelian.CommSq
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels

/-!
# Ordinary double-cokernel and intersection comparisons

A commuting square has its canonical double-cokernel comparison. The pullback
intersection lemma preserves the original subobject-closure hypotheses and
actual cokernel map. No Grothendieck group is used in this owner.
-/
@[expose] public section

open CategoryTheory.ExactCategory
open CategoryTheory.ObjectProperty



noncomputable section
universe v u
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open scoped ZeroObject

namespace Quillen.Devissage
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [Abelian C]
  (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderSubobjects]
  [P.IsClosedUnderQuotients] [P.IsClosedUnderFiniteProducts]

/-- Quotienting a commutative square in the two orders gives canonically
isomorphic double cokernels. This is the categorical diamond comparison. -/
def doubleCokernelSwap {I U A X : C} (t : I ⟶ U) (l : I ⟶ A)
    (r : U ⟶ X) (b : A ⟶ X) (w : t ≫ r = l ≫ b) :
    cokernel (cokernel.map t b l r w) ≅
      cokernel (cokernel.map l r t b w.symm) := by
  let m₁ := cokernel.map t b l r w
  let m₂ := cokernel.map l r t b w.symm
  have hb : b ≫ cokernel.π r ≫ cokernel.π m₂ = 0 := by
    rw [← assoc, ← cokernel.π_desc l (b ≫ cokernel.π r), assoc]
    change cokernel.π l ≫ m₂ ≫ cokernel.π m₂ = 0
    simp
  have hr : r ≫ cokernel.π b ≫ cokernel.π m₁ = 0 := by
    rw [← assoc, ← cokernel.π_desc t (r ≫ cokernel.π b), assoc]
    change cokernel.π t ≫ m₁ ≫ cokernel.π m₁ = 0
    simp
  let q₁ := cokernel.desc b (cokernel.π r ≫ cokernel.π m₂) hb
  let q₂ := cokernel.desc r (cokernel.π b ≫ cokernel.π m₁) hr
  have hm₁ : m₁ ≫ q₁ = 0 := by
    rw [← cancel_epi (cokernel.π t)]
    simp [m₁, q₁]
  have hm₂ : m₂ ≫ q₂ = 0 := by
    rw [← cancel_epi (cokernel.π l)]
    simp [m₂, q₂]
  exact
    { hom := cokernel.desc m₁ q₁ hm₁
      inv := cokernel.desc m₂ q₂ hm₂
      hom_inv_id := by
        rw [← cancel_epi (cokernel.π m₁), ← cancel_epi (cokernel.π b)]
        simp [q₁, q₂, m₁, m₂]
      inv_hom_id := by
        rw [← cancel_epi (cokernel.π m₂), ← cancel_epi (cokernel.π r)]
        simp [q₁, q₂, m₁, m₂] }

omit [P.ContainsZero] [P.IsClosedUnderQuotients] [P.IsClosedUnderFiniteProducts] in
/-- The quotient of an intersection in one subobject embeds in the quotient
by the other subobject. Thus this refinement factor still lies in `P`. -/
lemma pullback_cokernel_mem {I U A X : C} {t : I ⟶ U} {l : I ⟶ A}
    {r : U ⟶ X} {b : A ⟶ X} (sq : IsPullback t l r b)
    (hB : P (cokernel b)) : P (cokernel t) := by
  let := Abelian.mono_cokernel_map_of_isPullback sq
  exact P.prop_of_mono (cokernel.map t b l r sq.w) hB

end Quillen.Devissage
