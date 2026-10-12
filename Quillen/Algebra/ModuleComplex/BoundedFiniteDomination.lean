/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Algebra.ModuleComplex.FiniteDomination

/-! # Bounded finite-domination replacement

A bounded degreewise-projective cochain complex homotopy dominated through
finite module terms admits an actual homotopy-equivalent complex of finite
projective modules. The replacement retains both original zero bounds and the
specified domination through the same middle complex.

The proof is finite induction on the natural-number distance between the lower
zero bound and the cutoff of a finite upper tail. Each successor uses a genuine
finite-free split pivot. At the lower bound, the identity factors through a
finite module and yields finiteness by a surjection. Empty and singleton degree
intervals require no pivot. No finiteness of submodules, noetherianity, or
projectivity of images is assumed.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace Quillen.ModuleComplex.FiniteDomination

variable {R : Type u} [CommRing R]
  {C F : CochainComplex (ModuleCat.{u} R) ℤ}
  (i : C ⟶ F) (p : F ⟶ C) (H : Homotopy (𝟙 C) (i ≫ p))

include H in
/-- Descending finite induction converts the possibly infinite terms at and
above the lower bound into finite projective terms. The actual comparison and
both original zero bounds are retained. -/
theorem exists_finite_model_of_finite_above (a b : ℤ) (m : ℕ)
    (hcut : a + (m : ℤ) ≤ b)
    (hprojective : ∀ n, Module.Projective R (C.X n))
    (hlower : ∀ n, n < a → IsZero (C.X n))
    (hupper : ∀ n, b < n → IsZero (C.X n))
    (hfinite : ∀ n, a + (m : ℤ) < n → Module.Finite R (C.X n))
    (hF : ∀ n, Module.Finite R (F.X n)) :
    ∃ P : CochainComplex (ModuleCat.{u} R) ℤ,
      (∀ n, Module.Finite R (P.X n) ∧ Module.Projective R (P.X n)) ∧
      (∀ n, n < a → IsZero (P.X n)) ∧
      (∀ n, b < n → IsZero (P.X n)) ∧
      ∃ e : HomotopyEquiv C P,
        Nonempty (Homotopy (𝟙 P) ((e.inv ≫ i) ≫ (p ≫ e.hom))) := by
  induction m generalizing C with
  | zero =>
      have hCa : Module.Finite R (C.X a) := by
        let := hfinite (a + 1) (by omega)
        let := hF a
        exact finite_at_lower i p H a (hlower (a - 1) (by omega))
      refine ⟨C, fun n => ⟨?_, hprojective n⟩, hlower, hupper,
        HomotopyEquiv.refl C, ⟨transport i p H (HomotopyEquiv.refl C)⟩⟩
      rcases lt_trichotomy n a with hn | rfl | hn
      · let := ModuleCat.isZero_iff_subsingleton.mp (hlower n hn)
        infer_instance
      · exact hCa
      · exact hfinite n (by omega)
  | succ m ih =>
      let := hF (a + (m : ℤ) + 1)
      obtain ⟨D, hDp, hDl, hDu, hDf, e, ⟨h⟩⟩ :=
        exists_step i p H (a + (m : ℤ)) a b (by omega) (by omega)
          hprojective hlower hupper (fun n hn => hfinite n (by omega))
      obtain ⟨P, hP, hPl, hPu, e', _⟩ :=
        ih (e.inv ≫ i) (p ≫ e.hom) h (by omega) hDp hDl hDu hDf
      exact ⟨P, hP, hPl, hPu, e.trans e', ⟨transport i p H (e.trans e')⟩⟩

include H in
/-- Every bounded degreewise-projective complex homotopy dominated through
finite module terms has a bounded finite-projective replacement with an actual
homotopy equivalence. The same original bounds are preserved, including when
the interval is empty or contains a single degree. -/
theorem exists_bounded_finite_projective_model (a b : ℤ)
    (hprojective : ∀ n, Module.Projective R (C.X n))
    (hlower : ∀ n, n < a → IsZero (C.X n))
    (hupper : ∀ n, b < n → IsZero (C.X n))
    (hF : ∀ n, Module.Finite R (F.X n)) :
    ∃ P : CochainComplex (ModuleCat.{u} R) ℤ,
      (∀ n, Module.Finite R (P.X n) ∧ Module.Projective R (P.X n)) ∧
      (∀ n, n < a → IsZero (P.X n)) ∧
      (∀ n, b < n → IsZero (P.X n)) ∧
      ∃ e : HomotopyEquiv C P,
        Nonempty (Homotopy (𝟙 P) ((e.inv ≫ i) ≫ (p ≫ e.hom))) := by
  by_cases hab : a ≤ b
  · apply exists_finite_model_of_finite_above i p H a b (b - a).toNat
      (by omega) hprojective hlower hupper _ hF
    intro n hn
    let := ModuleCat.isZero_iff_subsingleton.mp (hupper n (by omega))
    infer_instance
  · refine ⟨C, fun n => ⟨?_, hprojective n⟩, hlower, hupper,
      HomotopyEquiv.refl C, ⟨transport i p H (HomotopyEquiv.refl C)⟩⟩
    have hz : IsZero (C.X n) := by
      by_cases hn : n < a
      · exact hlower n hn
      · exact hupper n (by omega)
    let := ModuleCat.isZero_iff_subsingleton.mp hz
    infer_instance

end Quillen.ModuleComplex.FiniteDomination
