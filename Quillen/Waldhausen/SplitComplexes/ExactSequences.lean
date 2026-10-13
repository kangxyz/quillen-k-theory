/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.SplitComplexes.Subcategory

/-!
# Split cofibrations and degreewise split exact sequences

This identifies the cofibrations of the split full-subcategory model with
actual degreewise split short exact sequences whose quotient lies in the
subcategory. The degreewise retractions are extended to full short-complex
splittings using exactness; no chain splitting is required.
-/
@[expose] public section


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe v u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.Waldhausen

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- A termwise retraction of the first map in a short exact sequence
extends to a full splitting of that sequence in each degree. -/
def degreewiseSplittingOfShortExact {S : ShortComplex (CochainComplex A ℤ)}
    (hS : S.ShortExact) (hf : degreewiseSplitMono S.f) (n : ℤ) :
    (S.map (eval A (ComplexShape.up ℤ) n)).Splitting := by
  let T := S.map (eval A (ComplexShape.up ℤ) n)
  have hT := (shortExact_iff_degreewise_shortExact S).1 hS n
  let : IsSplitMono T.f := hf n
  exact ShortComplex.Splitting.ofExactOfRetraction T hT.exact
    (retraction T.f) (IsSplitMono.id T.f) hT.epi_g

/-- Full degreewise splittings imply both actual short exactness and
termwise split-monomorphism of the first map. -/
theorem shortExact_and_degreewiseSplitMono_of_splittings
    {S : ShortComplex (CochainComplex A ℤ)}
    (h : ∀ n : ℤ, Nonempty (S.map (eval A (ComplexShape.up ℤ) n)).Splitting) :
    S.ShortExact ∧ degreewiseSplitMono S.f := by
  exact ⟨shortExact_of_degreewise_shortExact S (fun n ↦ (h n).some.shortExact),
    fun n ↦ (h n).some.isSplitMono_f⟩

variable (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]

/-- The cofibrations are precisely first arrows of actual degreewise split
short exact sequences with quotient in the full subcategory. -/
theorem splitSubcategoryCofibrations_iff {K L : P.FullSubcategory} (i : K ⟶ L) :
    splitSubcategoryCofibrations P i ↔
      ∃ (Z : CochainComplex A ℤ) (_hZ : P Z) (p : L.obj ⟶ Z) (hp : i.hom ≫ p = 0),
        ∀ n : ℤ, Nonempty
          ((ShortComplex.mk i.hom p hp).map (eval A (ComplexShape.up ℤ) n)).Splitting := by
  constructor
  · intro hi
    obtain ⟨Z, hZ, p, hp, hS⟩ :=
      (ExactSubcategory.inflation_iff (abelianExactStructure _) P i).1 hi.1
    exact ⟨Z, hZ, p, hp, fun n ↦ ⟨degreewiseSplittingOfShortExact hS hi.2 n⟩⟩
  · rintro ⟨Z, hZ, p, hp, h⟩
    obtain ⟨hS, hi⟩ := shortExact_and_degreewiseSplitMono_of_splittings h
    exact ⟨(ExactSubcategory.inflation_iff (abelianExactStructure _) P i).2
      ⟨Z, hZ, p, hp, hS⟩, hi⟩

end Quillen.Waldhausen
