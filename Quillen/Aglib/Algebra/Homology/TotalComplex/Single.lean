/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# Totalizing a complex concentrated in its second degree zero

The original chain complex embeds into the zero-th column of the actual
total complex. The explicit coproduct inverse proves this is a chain
isomorphism, with no homological or exactness assumption.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits

universe u

namespace HomologicalComplex₂

variable (K : ChainComplex (ModuleCat.{u} ℤ) ℕ)

/-- A chain complex regarded as a bicomplex supported in second degree zero. -/
def single₀Bicomplex : HomologicalComplex₂ (ModuleCat.{u} ℤ)
    (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  ((ChainComplex.single₀ (ModuleCat.{u} ℤ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj K

/-- The original complex includes in the actual total complex at second degree zero. -/
def single₀TotalInclusion : K ⟶ (single₀Bicomplex K).total (ComplexShape.down ℕ) where
  f n := (single₀Bicomplex K).ιTotal (ComplexShape.down ℕ) n 0 n (Nat.add_zero n)
  comm' i j h := by
    change _ ≫ ((single₀Bicomplex K).D₁ (ComplexShape.down ℕ) i j +
      (single₀Bicomplex K).D₂ (ComplexShape.down ℕ) i j) = K.d i j ≫ _
    rw [Preadditive.comp_add, ι_D₁, ι_D₂,
      d₁_eq _ _ h 0 j (Nat.add_zero j),
      d₂_eq_zero _ _ i 0 j (by simp)]
    simp [single₀Bicomplex, ComplexShape.ε₁]

/-- The degreewise projection discards the zero objects in positive second degree. -/
def single₀TotalProjection (n : ℕ) :
    ((single₀Bicomplex K).total (ComplexShape.down ℕ)).X n ⟶ K.X n :=
  (single₀Bicomplex K).totalDesc fun i j h ↦
    if hj : j = 0 then by
      subst j
      have hi : i = n := by simpa using h
      subst i
      exact 𝟙 _
    else 0

@[reassoc (attr := simp)]
theorem single₀TotalInclusion_projection (n : ℕ) :
    (single₀TotalInclusion K).f n ≫ single₀TotalProjection K n = 𝟙 _ := by
  simp [single₀TotalInclusion, single₀TotalProjection, single₀Bicomplex]

@[reassoc (attr := simp)]
theorem single₀TotalProjection_inclusion (n : ℕ) :
    single₀TotalProjection K n ≫ (single₀TotalInclusion K).f n = 𝟙 _ := by
  apply total.hom_ext
  intro i j h
  by_cases hj : j = 0
  · subst j
    have hi : i = n := by simpa using h
    subst i
    simp [single₀TotalProjection, single₀TotalInclusion]
  · apply (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0 (K.X i) j hj).eq_of_src

/-- Inclusion into the total of the single-row bicomplex is invertible degreewise. -/
instance single₀TotalInclusion_f_isIso (n : ℕ) : IsIso ((single₀TotalInclusion K).f n) :=
  ⟨⟨single₀TotalProjection K n, single₀TotalInclusion_projection K n,
    single₀TotalProjection_inclusion K n⟩⟩

/-- Concentration in second degree zero gives the original complex by an actual chain iso. -/
def single₀TotalIso : K ≅ (single₀Bicomplex K).total (ComplexShape.down ℕ) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ asIso ((single₀TotalInclusion K).f n))
    (fun i j _ ↦ (single₀TotalInclusion K).comm i j)

@[simp]
theorem single₀TotalIso_hom : (single₀TotalIso K).hom = single₀TotalInclusion K := rfl

end HomologicalComplex₂
