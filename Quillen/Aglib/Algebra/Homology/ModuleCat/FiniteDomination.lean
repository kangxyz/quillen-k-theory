/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.Algebra.Homology.ModuleCat.SplitPivot
public import Mathlib.RingTheory.Finiteness.Cardinality

/-! # Finite-domination replacement at one degree

An actual homotopy from the identity to a map through finite module terms
provides a finite-free split pivot whenever the next term is finite and the
current term is projective. The resulting whole-complex homotopy equivalence
preserves projectivity, a lower zero bound, and the previously finite upper
tail. The same domination transports along the actual equivalence.

At the bottom degree, the incoming differential vanishes. The identity then
factors through a finite module, proving finiteness by an actual surjection.
Neither argument uses noetherianity, finite submodules, or projective images.
These are the step and terminal case for descending finite-domination
replacement; this module does not yet assert the full induction or a geometric
strictification theorem.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace Quillen.ModuleComplex.FiniteDomination

variable {R : Type u} [CommRing R]
  {C F P : CochainComplex (ModuleCat.{u} R) ℤ}
  (i : C ⟶ F) (p : F ⟶ C) (H : Homotopy (𝟙 C) (i ≫ p))

/-- Conjugating the specified domination by an actual homotopy equivalence
retains its original middle complex. -/
def transport (e : HomotopyEquiv C P) :
    Homotopy (𝟙 P) ((e.inv ≫ i) ≫ (p ≫ e.hom)) := by
  have h := (H.compLeft e.inv).compRight e.hom
  simp only [Category.comp_id] at h
  exact e.homotopyInvHomId.symm.trans
    (h.trans (Homotopy.ofEq (by simp only [Category.assoc])))

/-- The two non-incoming homotopy terms factor through the next original term
and the original dominating term. -/
def defectReturn (n : ℤ) : C.X (n + 1) × F.X n →ₗ[R] C.X n :=
  (H.hom (n + 1) n).hom.coprod (p.f n).hom

/-- The actual map to the finite inputs retains the outgoing differential and
the original domination map. -/
def defectInput (n : ℤ) : C.X n →ₗ[R] C.X (n + 1) × F.X n :=
  (C.d n (n + 1)).hom.prod (i.f n).hom

/-- The homotopy identity is the required incoming split identity plus the
specified finite-factor defect. -/
theorem differential_add_defect (k : ℤ) :
    (C.d k (k + 1)).hom.comp (H.hom (k + 1) k).hom +
      (defectReturn (i := i) p H (k + 1)).comp (defectInput i (k + 1)) = LinearMap.id := by
  have h := H.comm (k + 1)
  rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (k + 1) (k + 1 + 1) by rfl),
    prevD_eq _ (show (ComplexShape.up ℤ).Rel k (k + 1) by rfl)] at h
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp h) x
  change x = H.hom (k + 1 + 1) (k + 1) (C.d (k + 1) (k + 1 + 1) x) +
    C.d k (k + 1) (H.hom (k + 1) k x) + p.f (k + 1) (i.f (k + 1) x) at hx
  change C.d k (k + 1) (H.hom (k + 1) k x) +
    (H.hom (k + 1 + 1) (k + 1) (C.d (k + 1) (k + 1 + 1) x) +
      p.f (k + 1) (i.f (k + 1) x)) = x
  simpa only [add_assoc, add_comm, add_left_comm] using hx.symm

/-- Projectivity lifts the actual defect input through a finite-free cover.
The resulting finite-free right defect gives a genuine split pivot. -/
theorem exists_finite_free_split (k : ℤ)
    [Module.Projective R (C.X (k + 1))]
    [Module.Finite R (C.X (k + 1 + 1))] [Module.Finite R (F.X (k + 1))] :
    ∃ (m : ℕ) (r : (Fin m → R) →ₗ[R] C.X (k + 1))
      (t : C.X (k + 1) →ₗ[R] Fin m → R),
      (C.d k (k + 1)).hom.comp (H.hom (k + 1) k).hom + r.comp t = LinearMap.id := by
  obtain ⟨m, q, hq⟩ := Module.Finite.exists_fin' R (C.X (k + 1 + 1) × F.X (k + 1))
  obtain ⟨t, ht⟩ := Module.projective_lifting_property q (defectInput i (k + 1)) hq
  refine ⟨m, (defectReturn (i := i) p H (k + 1)).comp q, t, ?_⟩
  rw [LinearMap.comp_assoc, ht]
  exact differential_add_defect i p H k

include H in
/-- A finite upper tail and actual finite domination yield a homotopy-equivalent
replacement with one more finite degree, retaining every projective term and
any original lower zero bound at or below the lower pivot. -/
theorem exists_step (k a b : ℤ) (ha : a ≤ k) (hb : k + 1 ≤ b)
    (hprojective : ∀ n, Module.Projective R (C.X n))
    (hlower : ∀ n, n < a → IsZero (C.X n))
    (hupper : ∀ n, b < n → IsZero (C.X n))
    (hfinite : ∀ n, k + 1 < n → Module.Finite R (C.X n))
    [Module.Finite R (F.X (k + 1))] :
    ∃ P : CochainComplex (ModuleCat.{u} R) ℤ,
      (∀ n, Module.Projective R (P.X n)) ∧
      (∀ n, n < a → IsZero (P.X n)) ∧
      (∀ n, b < n → IsZero (P.X n)) ∧
      (∀ n, k < n → Module.Finite R (P.X n)) ∧
      ∃ e : HomotopyEquiv C P,
        Nonempty (Homotopy (𝟙 P) ((e.inv ≫ i) ≫ (p ≫ e.hom))) := by
  let := hprojective (k + 1)
  let := hfinite (k + 1 + 1) (by omega)
  obtain ⟨m, r, t, hs⟩ := exists_finite_free_split i p H k
  let G := ModuleCat.of R (Fin m → R)
  let s := (H.hom (k + 1) k).hom
  let P := SplitPivot.replacement C k G r
  let e := SplitPivot.homotopyEquiv C k G s r t hs
  refine ⟨P, ?_, SplitPivot.replacement_preserves_lower_bound C k G r a ha hlower,
    ?_, ?_, e, ⟨transport i p H e⟩⟩
  · intro n
    by_cases h : n = k
    · subst n
      let := hprojective k
      let := SplitPivot.projective_kernel C k G s r t hs
      exact Module.Projective.of_equiv (SplitPivot.lowerIso C k G r).toLinearEquiv.symm
    · by_cases h' : n = k + 1
      · subst n
        exact SplitPivot.projective_replacement_upper C k G r
      · let := hprojective n
        exact Module.Projective.of_equiv
          (SplitPivot.otherIso C k G r n h h').toLinearEquiv.symm
  · intro n hn
    exact (hupper n hn).of_iso
      (SplitPivot.otherIso C k G r n (by omega) (by omega))
  · intro n hn
    by_cases h : n = k + 1
    · subst n
      exact SplitPivot.finite_replacement_upper C k G r
    · let := hfinite n (by omega)
      exact Module.Finite.equiv
        (SplitPivot.otherIso C k G r n (by omega) h).toLinearEquiv.symm

/-- At an original lower zero bound, the incoming homotopy term vanishes and
the remaining finite-factor return map is genuinely surjective. -/
theorem defectReturn_surjective_at_lower (a : ℤ) (hlower : IsZero (C.X (a - 1))) :
    Function.Surjective (defectReturn (i := i) p H a) := by
  intro x
  refine ⟨defectInput i a x, ?_⟩
  have h := H.comm a
  rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel a (a + 1) by rfl),
    prevD_eq _ (show (ComplexShape.up ℤ).Rel (a - 1) a by dsimp; omega)] at h
  have hz : C.d (a - 1) a = 0 := hlower.eq_of_src _ _
  have hx := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp h) x
  simpa [defectReturn, defectInput, hz] using hx.symm

include H in
/-- The terminal cutoff is finite by a genuine surjection from the finite
upper and dominating terms; no projectivity assumption is needed here. -/
theorem finite_at_lower (a : ℤ) (hlower : IsZero (C.X (a - 1)))
    [Module.Finite R (C.X (a + 1))] [Module.Finite R (F.X a)] :
    Module.Finite R (C.X a) :=
  Module.Finite.of_surjective (defectReturn (i := i) p H a)
    (defectReturn_surjective_at_lower i p H a hlower)

end Quillen.ModuleComplex.FiniteDomination
