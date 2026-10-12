/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Algebra.Homology.ConnectingKernel
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! # Consumers of the connecting-kernel comparison and its sign convention -/

@[expose] public section

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe u

namespace Tests.ConnectingKernel

variable {S : ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ)}
  (hS : S.ShortExact) (n : ℕ)

/-- The ordinary relative homology shift follows from epimorphisms in every degree. -/
def relativeHomologyKernelIso
    (hEpi : ∀ k, Epi (HomologicalComplex.homologyMap S.f k)) :
    S.X₃.homology (n + 1) ≅ kernel (HomologicalComplex.homologyMap S.f n) :=
  have := hEpi (n + 1)
  hS.connectingKernelIso (n + 1) n rfl

/-- The actual long-exact-sequence boundary, rather than an abstract replacement,
is the composite with the kernel inclusion. -/
example [Epi (HomologicalComplex.homologyMap S.f (n + 1))] :
    (hS.connectingKernelIso (n + 1) n rfl).hom ≫
        kernel.ι (HomologicalComplex.homologyMap S.f n) = hS.δ (n + 1) n rfl :=
  hS.connectingKernelIso_hom_ι (n + 1) n rfl

/-- The inverse also preserves the actual kernel inclusion. -/
example [Epi (HomologicalComplex.homologyMap S.f (n + 1))] :
    (hS.connectingKernelIso (n + 1) n rfl).inv ≫ hS.δ (n + 1) n rfl =
      kernel.ι (HomologicalComplex.homologyMap S.f n) :=
  hS.connectingKernelIso_inv_δ (n + 1) n rfl

/-- The kernel coordinate is the first summand. -/
example (X : ModuleCat.{u} ℤ) :
    (kernelAdditionIso X).hom =
      kernel.ι (biprod.desc (𝟙 X) (𝟙 X)) ≫ biprod.fst := by
  simp

/-- Positive first coordinate in the inverse. -/
example (X : ModuleCat.{u} ℤ) :
    (kernelAdditionIso X).inv ≫ kernel.ι (biprod.desc (𝟙 X) (𝟙 X)) ≫
      biprod.fst = 𝟙 X := by
  simp

/-- Negative second coordinate in the inverse. -/
example (X : ModuleCat.{u} ℤ) :
    (kernelAdditionIso X).inv ≫ kernel.ι (biprod.desc (𝟙 X) (𝟙 X)) ≫
      biprod.snd = -𝟙 X := by
  simp

end Tests.ConnectingKernel
