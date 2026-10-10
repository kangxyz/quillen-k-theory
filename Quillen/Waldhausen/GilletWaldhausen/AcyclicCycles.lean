/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Resolution.Finite
public import Quillen.CategoryTheory.ExactCategory.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Data.Int.Init

/-!
# Actual cycle sequences and kernel-closed subcategories

For an upper-bounded acyclic cochain complex with all terms in a replete
kernel-closed full subcategory of an abelian category, all cycle objects
belong to that subcategory. The actual maps from cycles into a term and
from that term onto the next cycles form a short exact sequence.

This is the algebraic cycle-closure input used by the acyclic truncation
induction in Thomason–Trobaugh 1.11.7–1.11.8. No K-theory comparison,
additivity, or localization conclusion is assumed or asserted.
-/
@[expose] public section


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe v u

namespace Quillen.Waldhausen.GilletWaldhausen

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The genuine cycle inclusion followed by the next cycle projection vanishes. -/
@[reassoc (attr := simp)]
theorem iCycles_toCycles (K : CochainComplex A ℤ) (n : ℤ) :
    K.iCycles n ≫ K.toCycles n (n + 1) = 0 := by
  rw [← cancel_mono (K.iCycles (n + 1)), Category.assoc, K.toCycles_i,
    K.iCycles_d, zero_comp]

/-- The actual cycle/term/next-cycle sequence. -/
def cycleSequence (K : CochainComplex A ℤ) (n : ℤ) : ShortComplex A :=
  ShortComplex.mk (K.iCycles n) (K.toCycles n (n + 1)) (iCycles_toCycles K n)

/-- Exactness in the next degree makes the actual map onto its cycles epi. -/
theorem epi_toCycles_of_exactAt (K : CochainComplex A ℤ) (n : ℤ)
    (hK : K.ExactAt (n + 1)) : Epi (K.toCycles n (n + 1)) := by
  have hs := (K.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp; omega)).1 hK
  let e := K.cyclesIsoSc' n (n + 1) (n + 2) (by simp) (by simp; omega)
  have : Epi (K.toCycles n (n + 1) ≫ e.hom) := by
    rw [K.toCycles_cyclesIsoSc'_hom]
    exact hs.epi_toCycles
  exact (epi_comp_iff_of_isIso (K.toCycles n (n + 1)) e.hom).1 inferInstance

/-- The cycle sequence is short exact whenever the next degree is exact. -/
theorem cycleSequence_shortExact (K : CochainComplex A ℤ) (n : ℤ)
    (hK : K.ExactAt (n + 1)) : (cycleSequence K n).ShortExact where
  mono_f := inferInstanceAs (Mono (K.iCycles n))
  epi_g := epi_toCycles_of_exactAt K n hK
  exact := (cycleSequence K n).exact_of_f_is_kernel
    (isKernelOfComp (K.iCycles (n + 1)) (K.d n (n + 1))
      (K.cyclesIsKernel n (n + 1) (by simp)) (iCycles_toCycles K n) (K.toCycles_i n (n + 1)))

attribute [local instance] Abelian.hasFiniteBiproducts

variable (P : ObjectProperty A) [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsKernelClosed P]
  (K : CochainComplex A ℤ) (hterms : ∀ n, P (K.X n))
  (hK : K.Acyclic) (b : ℤ) (hb : ∀ n, b < n → IsZero (K.X n))

include hterms hK hb in
/-- Downward induction from the strict upper bound puts every actual cycle
in the chosen kernel-closed subcategory. No lower bound is required. -/
theorem cycles_mem (n : ℤ) : P (K.cycles n) := by
  have top (i : ℤ) (hi : b ≤ i) : P (K.cycles i) :=
    P.prop_of_iso (K.iCyclesIso i (i + 1) (by simp)
      ((hb (i + 1) (by omega)).eq_of_tgt _ _)).symm (hterms i)
  by_cases hn : n ≤ b
  · induction n, hn using Int.leInductionDown with
    | base => exact top b le_rfl
    | pred n hn ih =>
        apply ExactStructure.IsKernelClosed.prop_kernel (E := abelianExactStructure A)
          (cycleSequence_shortExact K (n - 1) (hK _)) (hterms _)
        simpa only [cycleSequence, sub_add_cancel] using ih
  · exact top n (by omega)

section FullSubcategory

variable [P.ContainsZero] [(abelianExactStructure A).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]

/-- The cycle sequence as an actual short complex in the full subcategory,
retaining the original ambient cycle and differential maps. -/
def subcategoryCycleSequence (n : ℤ) : ShortComplex P.FullSubcategory :=
  ShortComplex.mk
    (P.homMk (K.iCycles n) : (⟨K.cycles n, cycles_mem P K hterms hK b hb n⟩ : P.FullSubcategory) ⟶
      ⟨K.X n, hterms n⟩)
    (P.homMk (K.toCycles n (n + 1)) : (⟨K.X n, hterms n⟩ : P.FullSubcategory) ⟶
      ⟨K.cycles (n + 1), cycles_mem P K hterms hK b hb (n + 1)⟩)
    (ObjectProperty.hom_ext _ (iCycles_toCycles K n))

/-- The lifted cycle sequence is a genuine conflation in the inherited
exact structure, not merely a relation in a derived category. -/
theorem subcategoryCycleSequence_conflation (n : ℤ) :
    (ExactSubcategory.exactStructure (abelianExactStructure A) P).conflation
      (subcategoryCycleSequence P K hterms hK b hb n) :=
  cycleSequence_shortExact K n (hK (n + 1))

end FullSubcategory

end Quillen.Waldhausen.GilletWaldhausen
