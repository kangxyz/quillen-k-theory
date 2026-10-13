/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Abelian.Exact


/-!
# Actual homology, opcycle and next-boundary short exact sequences

For an arbitrary cochain complex in an abelian category, the next boundary is
constructed as the cokernel of the original homology-to-opcycles inclusion.
Both original short exact sequences and the literal factorization of the
outgoing differential are retained. There is no boundedness or acyclicity premise.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace Quillen.CochainComplex
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The next boundary object as the actual quotient of opcycles by homology. -/
def boundaryAfter (K : CochainComplex C ℤ) (n : ℤ) : C := cokernel (K.homologyι n)

/-- The actual homology/opcycle/boundary sequence. -/
def opcycleBoundarySequence (K : CochainComplex C ℤ) (n : ℤ) : ShortComplex C :=
  ShortComplex.mk (K.homologyι n) (cokernel.π (K.homologyι n)) (cokernel.condition _)

lemma opcycleBoundarySequence_shortExact (K : CochainComplex C ℤ) (n : ℤ) :
    (opcycleBoundarySequence K n).ShortExact where
  exact := ShortComplex.exact_cokernel _
  mono_f := inferInstanceAs (Mono (K.homologyι n))
  epi_g := inferInstanceAs (Epi (cokernel.π (K.homologyι n)))

/-- The next boundary includes in the original next term. -/
def boundaryAfterι (K : CochainComplex C ℤ) (n : ℤ) : boundaryAfter K n ⟶ K.X (n + 1) :=
  cokernel.desc (K.homologyι n) (K.fromOpcycles n (n + 1)) (by simp)

@[reassoc (attr := simp)]
lemma boundaryAfter_π_ι (K : CochainComplex C ℤ) (n : ℤ) :
    cokernel.π (K.homologyι n) ≫ boundaryAfterι K n = K.fromOpcycles n (n + 1) :=
  cokernel.π_desc _ _ _

instance boundaryAfterι_mono (K : CochainComplex C ℤ) (n : ℤ) : Mono (boundaryAfterι K n) := by
  let S := ShortComplex.mk (K.homologyι n) (K.fromOpcycles n (n + 1)) (by simp)
  have hS : S.Exact := S.exact_of_f_is_kernel (K.homologyIsKernel n (n + 1) (by simp))
  exact hS.mono_cokernelDesc

@[reassoc (attr := simp)]
lemma boundaryAfterι_pOpcycles (K : CochainComplex C ℤ) (n : ℤ) :
    boundaryAfterι K n ≫ K.pOpcycles (n + 1) = 0 := by
  rw [← cancel_epi (cokernel.π (K.homologyι n)), boundaryAfter_π_ι_assoc, comp_zero]
  rw [← cancel_epi (K.pOpcycles n), ← Category.assoc, K.p_fromOpcycles]
  simp

/-- The actual next-boundary/term/opcycle sequence. -/
def boundaryOpcycleSequence (K : CochainComplex C ℤ) (n : ℤ) : ShortComplex C :=
  ShortComplex.mk (boundaryAfterι K n) (K.pOpcycles (n + 1)) (boundaryAfterι_pOpcycles K n)

lemma boundaryOpcycleSequence_shortExact (K : CochainComplex C ℤ) (n : ℤ) :
    (boundaryOpcycleSequence K n).ShortExact := by
  let S := ShortComplex.mk (K.d n (n + 1)) (K.pOpcycles (n + 1)) (by simp)
  let T := ShortComplex.mk (K.fromOpcycles n (n + 1)) (K.pOpcycles (n + 1)) (by
    rw [← cancel_epi (K.pOpcycles n), ← Category.assoc, K.p_fromOpcycles]
    simp)
  have hS : S.Exact := S.exact_of_g_is_cokernel (K.opcyclesIsCokernel n (n + 1) (by simp))
  let f : S ⟶ T :=
    { τ₁ := K.pOpcycles n
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [S, T] }
  have hT : T.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono f).mp hS
  let g : T ⟶ boundaryOpcycleSequence K n :=
    { τ₁ := cokernel.π (K.homologyι n)
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [T, boundaryOpcycleSequence] }
  exact { exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono g).mp hT
          mono_f := inferInstanceAs (Mono (boundaryAfterι K n))
          epi_g := inferInstanceAs (Epi (K.pOpcycles (n + 1))) }

end Quillen.CochainComplex
