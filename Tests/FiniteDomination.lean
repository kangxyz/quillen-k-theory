/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Algebra.ModuleComplex.FiniteDomination
public import Mathlib.Algebra.Homology.QuasiIso

/-! # Consumers of finite-domination replacement

One genuine finite-free pivot followed by the terminal finite-factor argument
produces a strict finite-projective model when only the two lowest terms may
still be infinite. Its original lower and upper bounds are retained, and its
actual comparison map is a quasi-isomorphism. The terminal argument is also
used independently without projectivity assumptions.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Quillen.ModuleComplex.FiniteDomination

namespace Quillen.Tests.FiniteDomination

variable {R : Type u} [CommRing R]
  {C F : CochainComplex (ModuleCat.{u} R) ℤ}
  (i : C ⟶ F) (p : F ⟶ C) (H : Homotopy (𝟙 C) (i ≫ p))

include H in
/-- The lowest original term is finite even when neither it nor the dominating
terms have been assumed projective. -/
theorem finite_lowest_term (a : ℤ) (hlower : ∀ n, n < a → IsZero (C.X n))
    [Module.Finite R (C.X (a + 1))] [Module.Finite R (F.X a)] :
    Module.Finite R (C.X a) :=
  finite_at_lower i p H a (hlower (a - 1) (by omega))

include H in
/-- One pivot and the terminal argument give an actual strict finite-projective
model, preserving the original bounds and original complex's homology. -/
theorem exists_model_of_two_remaining_degrees (a b : ℤ) (hab : a + 1 ≤ b)
    (hprojective : ∀ n, Module.Projective R (C.X n))
    (hlower : ∀ n, n < a → IsZero (C.X n))
    (hupper : ∀ n, b < n → IsZero (C.X n))
    (hfinite : ∀ n, a + 1 < n → Module.Finite R (C.X n))
    (hF : ∀ n, Module.Finite R (F.X n)) :
    ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ) (f : C ⟶ P),
      QuasiIso f ∧ (∀ n, n < a → IsZero (P.X n)) ∧
      (∀ n, b < n → IsZero (P.X n)) ∧
      (∀ n, Module.Finite R (P.X n) ∧ Module.Projective R (P.X n)) := by
  let := hF (a + 1)
  obtain ⟨P, hPp, hPl, hPu, hPf, e, ⟨h⟩⟩ :=
    exists_step i p H a a b le_rfl hab hprojective hlower hupper hfinite
  have hPa : Module.Finite R (P.X a) := by
    let := hPf (a + 1) (by omega)
    let := hF a
    exact finite_at_lower (e.inv ≫ i) (p ≫ e.hom) h a (hPl (a - 1) (by omega))
  refine ⟨P, e.hom, e.quasiIso_hom, hPl, hPu, fun n => ⟨?_, hPp n⟩⟩
  rcases lt_trichotomy n a with hn | rfl | hn
  · let := ModuleCat.isZero_iff_subsingleton.mp (hPl n hn)
    infer_instance
  · exact hPa
  · exact hPf n hn

end Quillen.Tests.FiniteDomination
