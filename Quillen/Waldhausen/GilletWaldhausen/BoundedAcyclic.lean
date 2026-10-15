/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.GilletWaldhausen.AcyclicCycles
public import Quillen.Waldhausen.ComplexSubcategory

/-! # Actual bounded acyclic complexes in a termwise exact subcategory -/
@[expose] public section

open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped ZeroObject
universe v u

namespace Quillen.Waldhausen.GilletWaldhausen

attribute [local instance] Abelian.hasFiniteBiproducts

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Strict term bounds, rather than a condition merely on homology. -/
def TermBounded (K : CochainComplex A ℤ) : Prop :=
  ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (K.X n)

/-- Actual bounded, termwise-P, acyclic complexes. -/
def boundedAcyclic (P : ObjectProperty A) : ObjectProperty (CochainComplex A ℤ) := fun K ↦
  TermBounded K ∧ (∀ n : ℤ, P (K.X n)) ∧ K.Acyclic

variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]

/-- Any actual zero complex belongs to this category. -/
theorem boundedAcyclic_of_isZero {K : CochainComplex A ℤ} (hK : IsZero K) :
    boundedAcyclic P K := by
  have hz (n : ℤ) := (eval A (ComplexShape.up ℤ) n).map_isZero hK
  exact ⟨⟨0, 0, fun n _ ↦ hz n⟩, fun n ↦ P.prop_of_isZero (hz n),
    acyclic_of_isZero K hK⟩

instance boundedAcyclic_containsZero : (boundedAcyclic P).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, boundedAcyclic_of_isZero P (isZero_zero _)⟩

/-- The predicate is replete under actual chain isomorphisms. -/
instance boundedAcyclic_closedUnderIsomorphisms :
    (boundedAcyclic P).IsClosedUnderIsomorphisms where
  of_iso e hK := by
    obtain ⟨⟨a, b, hab⟩, hterms, hacyclic⟩ := hK
    let en (n : ℤ) := (eval A (ComplexShape.up ℤ) n).mapIso e
    exact ⟨⟨a, b, fun n hn ↦ (hab n hn).of_iso (en n).symm⟩,
      fun n ↦ P.prop_of_iso (en n) (hterms n), fun n ↦ (hacyclic n).of_iso e⟩

variable [(abelianExactStructure A).IsExtensionClosed P]

omit [P.ContainsZero] [P.IsClosedUnderIsomorphisms] in
/-- Bounds, term membership and acyclicity are all retained by genuine
short exact extensions of cochain complexes. -/
theorem boundedAcyclic_of_shortExact {S : ShortComplex (CochainComplex A ℤ)}
    (hS : S.ShortExact) (h₁ : boundedAcyclic P S.X₁) (h₃ : boundedAcyclic P S.X₃) :
    boundedAcyclic P S.X₂ := by
  obtain ⟨⟨a, b, hab⟩, ht₁, ha₁⟩ := h₁
  obtain ⟨⟨c, d, hcd⟩, ht₃, ha₃⟩ := h₃
  have hs (n : ℤ) := (shortExact_iff_degreewise_shortExact S).1 hS n
  refine ⟨⟨min a c, max b d, fun n hn ↦ ?_⟩, ?_, hS.acyclic_X₂ ha₁ ha₃⟩
  · have hz₁ := hab n (hn.elim
      (fun h ↦ Or.inl (lt_of_lt_of_le h (min_le_left _ _)))
      (fun h ↦ Or.inr (lt_of_le_of_lt (le_max_left _ _) h)))
    have hz₃ := hcd n (hn.elim
      (fun h ↦ Or.inl (lt_of_lt_of_le h (min_le_right _ _)))
      (fun h ↦ Or.inr (lt_of_le_of_lt (le_max_right _ _) h)))
    exact (hs n).exact.isZero_X₂ (hz₁.eq_of_src _ _) (hz₃.eq_of_tgt _ _)
  · intro n
    exact CategoryTheory.ExactCategory.ExactStructure.IsExtensionClosed.prop_middle (E :=
      abelianExactStructure A)
      (hs n) (ht₁ n) (ht₃ n)

instance boundedAcyclic_extensionClosed :
    (abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed (boundedAcyclic P) where
  prop_middle := boundedAcyclic_of_shortExact P

instance boundedAcyclic_closedUnderFiniteProducts :
    (boundedAcyclic P).IsClosedUnderFiniteProducts :=
  (abelianExactStructure (CochainComplex A ℤ)).extensionClosed_finiteProducts (boundedAcyclic P)

/-- The inherited exact structure on actual bounded acyclic complexes. -/
def boundedAcyclicExactStructure :=
  ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex A ℤ)) (boundedAcyclic P)

end Quillen.Waldhausen.GilletWaldhausen
