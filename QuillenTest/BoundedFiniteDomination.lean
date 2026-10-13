/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Algebra.ModuleComplex.BoundedFiniteDomination
public import Mathlib.Algebra.Homology.QuasiIso

/-! # Original-map consumers of bounded finite domination

The finite-projective replacement gives quasi-isomorphisms in both directions.
Its induced maps to and from the original dominating complex recover both
original maps up to explicit homotopies. The support bounds are unchanged.
The empty-interval consumer checks that the actual comparison is zero, while
the singleton consumer proves finiteness of the original term without assuming
projectivity or finiteness of a submodule.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Quillen.ModuleComplex.FiniteDomination

namespace QuillenTest.BoundedFiniteDomination

open Quillen

variable {R : Type u} [CommRing R]
  {C F : CochainComplex (ModuleCat.{u} R) ℤ}
  (i : C ⟶ F) (p : F ⟶ C) (H : Homotopy (𝟙 C) (i ≫ p))

include H in
/-- Both original domination maps are recovered by the actual comparison, and
both directions of that comparison preserve the original complex's homology. -/
theorem exists_model_with_original_maps (a b : ℤ)
    (hprojective : ∀ n, Module.Projective R (C.X n))
    (hlower : ∀ n, n < a → IsZero (C.X n))
    (hupper : ∀ n, b < n → IsZero (C.X n))
    (hF : ∀ n, Module.Finite R (F.X n)) :
    ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ) (e : HomotopyEquiv C P)
      (u : P ⟶ F) (v : F ⟶ P),
      (∀ n, Module.Finite R (P.X n) ∧ Module.Projective R (P.X n)) ∧
      (∀ n, n < a → IsZero (P.X n)) ∧
      (∀ n, b < n → IsZero (P.X n)) ∧
      QuasiIso e.hom ∧ QuasiIso e.inv ∧
      Nonempty (Homotopy (e.hom ≫ u) i) ∧
      Nonempty (Homotopy (v ≫ e.inv) p) ∧
      Nonempty (Homotopy (𝟙 P) (u ≫ v)) := by
  obtain ⟨P, hP, hPl, hPu, e, h⟩ :=
    exists_bounded_finite_projective_model i p H a b hprojective hlower hupper hF
  refine ⟨P, e, e.inv ≫ i, p ≫ e.hom, hP, hPl, hPu,
    e.quasiIso_hom, e.quasiIso_inv, ⟨?_⟩, ⟨?_⟩, h⟩
  · simpa only [Category.assoc] using e.homotopyHomInvId.compRightId i
  · simpa only [Category.assoc] using e.homotopyHomInvId.compLeftId p

include H in
/-- An empty original support interval is handled without an ordering
assumption on the bounds; the actual homotopy comparison is the zero map. -/
theorem exists_zero_comparison_of_empty_interval (a b : ℤ) (hab : b < a)
    (hprojective : ∀ n, Module.Projective R (C.X n))
    (hlower : ∀ n, n < a → IsZero (C.X n))
    (hupper : ∀ n, b < n → IsZero (C.X n))
    (hF : ∀ n, Module.Finite R (F.X n)) :
    ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ) (e : HomotopyEquiv C P),
      (∀ n, Module.Finite R (P.X n) ∧ Module.Projective R (P.X n)) ∧
      (∀ n, IsZero (P.X n)) ∧ e.hom = 0 := by
  obtain ⟨P, hP, hPl, hPu, e, _⟩ :=
    exists_bounded_finite_projective_model i p H a b hprojective hlower hupper hF
  have hPz : ∀ n, IsZero (P.X n) := by
    intro n
    by_cases hn : n < a
    · exact hPl n hn
    · exact hPu n (by omega)
  refine ⟨P, e, hP, hPz, ?_⟩
  apply HomologicalComplex.Hom.ext
  funext n
  exact (hPz n).eq_of_tgt _ _

include H in
/-- For a singleton support interval the original term is already finite;
there is no projectivity hypothesis and no adjacent replacement. -/
theorem finite_original_term_of_singleton_support (a : ℤ)
    (hlower : ∀ n, n < a → IsZero (C.X n))
    (hupper : ∀ n, a < n → IsZero (C.X n))
    [Module.Finite R (F.X a)] : Module.Finite R (C.X a) := by
  let := ModuleCat.isZero_iff_subsingleton.mp (hupper (a + 1) (by omega))
  exact finite_at_lower i p H a (hlower (a - 1) (by omega))

end QuillenTest.BoundedFiniteDomination
