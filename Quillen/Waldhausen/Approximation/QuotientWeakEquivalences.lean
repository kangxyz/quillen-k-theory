/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.Complexes
public import Quillen.CategoryTheory.ExactCategory.Abelian

/-!
# Quasi-isomorphisms on actual filtration quotients

A commutative square between ambient-monomorphism arrows with
quasi-isomorphic vertical maps induces a quasi-isomorphism on their actual
cokernels. This is the short-exact homology theorem, not an assumed quotient
comparison. It applies to every interval of a replaced finite filtration.
-/
@[expose] public section


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe v u

namespace Quillen.Waldhausen

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The actual cokernel sequence of a monomorphism of complexes is short exact. -/
theorem mono_cokernel_shortExact {K L : CochainComplex A ℤ} (i : K ⟶ L) [Mono i] :
    (ShortComplex.mk i (cokernel.π i) (cokernel.condition i)).ShortExact where
  exact := ShortComplex.cokernelSequence_exact i

/-- Quasi-isomorphisms on both terms induce a quasi-isomorphism on the
actual quotient of a monomorphism. -/
theorem cokernel_map_quasiIso {K L K' L' : CochainComplex A ℤ}
    (i : K ⟶ L) (i' : K' ⟶ L') [Mono i] [Mono i']
    (a : K ⟶ K') (b : L ⟶ L') (h : i ≫ b = a ≫ i')
    [QuasiIso a] [QuasiIso b] : QuasiIso (cokernel.map i i' a b h) := by
  let φ : ShortComplex.mk i (cokernel.π i) (cokernel.condition i) ⟶
      ShortComplex.mk i' (cokernel.π i') (cokernel.condition i') := {
    τ₁ := a
    τ₂ := b
    τ₃ := cokernel.map i i' a b h
    comm₁₂ := h.symm
    comm₂₃ := by simp }
  exact HomologySequence.quasiIso_τ₃ φ (mono_cokernel_shortExact i)
    (mono_cokernel_shortExact i') inferInstance inferInstance

end Quillen.Waldhausen
