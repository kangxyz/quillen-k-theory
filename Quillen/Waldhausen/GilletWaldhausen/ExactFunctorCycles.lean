/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.GilletWaldhausen.AcyclicCycles

/-!
# Acyclicity from mapped cycle sequences

An additive functor between abelian categories carries a cochain complex to an
acyclic complex whenever it carries every actual cycle sequence to a short
exact sequence. The functor need not be exact on the ambient category.
-/
@[expose] public section

open Quillen.Waldhausen.GilletWaldhausen



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u v u' v'
namespace Quillen.HomologicalAlgebra
open Waldhausen.GilletWaldhausen
variable {A : Type u} [Category.{v} A] [Abelian A]
  {B : Type u'} [Category.{v'} B] [Abelian B]

/-- Exactness of all actual mapped cycle sequences implies acyclicity of the
termwise image, without an ambient exactness assumption on the functor. -/
theorem acyclic_map_of_cycle_sequences (F : A ⥤ B) [F.Additive]
    (K : CochainComplex A ℤ)
    (h : ∀ n : ℤ, ((cycleSequence K n).map F).ShortExact) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic := by
  have he (n : ℤ) : ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).ExactAt (n + 1) := by
    let S : ShortComplex B := ShortComplex.mk
      (F.map (K.toCycles n (n + 1)) ≫ F.map (K.iCycles (n + 1)))
      (F.map (K.toCycles (n + 1) (n + 1 + 1))) (by
        rw [Category.assoc, ← F.map_comp, iCycles_toCycles, F.map_zero, comp_zero])
    let T := (cycleSequence K (n + 1)).map F
    let a : S ⟶ T :=
      { τ₁ := F.map (K.toCycles n (n + 1))
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _
        comm₁₂ := by simp [S, T, cycleSequence]
        comm₂₃ := by simp [S, T, cycleSequence] }
    have : Epi a.τ₁ := (h n).epi_g
    have : IsIso a.τ₂ := inferInstanceAs (IsIso (𝟙 _))
    have : Mono a.τ₃ := inferInstanceAs (Mono (𝟙 _))
    have hs : S.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono a).mpr (h (n + 1)).exact
    let C := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
    let b : S ⟶ C.sc' n (n + 1) (n + 1 + 1) :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := F.map (K.iCycles (n + 1 + 1))
        comm₁₂ := by
          change 𝟙 _ ≫ F.map (K.d n (n + 1)) =
            (F.map (K.toCycles n (n + 1)) ≫ F.map (K.iCycles (n + 1))) ≫ 𝟙 _
          rw [Category.id_comp, Category.comp_id, ← F.map_comp, K.toCycles_i]
        comm₂₃ := by
          change 𝟙 _ ≫ F.map (K.d (n + 1) (n + 1 + 1)) =
            F.map (K.toCycles (n + 1) (n + 1 + 1)) ≫ F.map (K.iCycles (n + 1 + 1))
          rw [Category.id_comp, ← F.map_comp, K.toCycles_i] }
    have : Epi b.τ₁ := inferInstanceAs (Epi (𝟙 _))
    have : IsIso b.τ₂ := inferInstanceAs (IsIso (𝟙 _))
    have : Mono b.τ₃ := (h (n + 1 + 1)).mono_f
    exact (C.exactAt_iff' n (n + 1) (n + 1 + 1) (by simp) (by simp)).mpr
      ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono b).mp hs)
  intro n
  simpa using he (n - 1)
end Quillen.HomologicalAlgebra
