/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Algebra.Homology.EventualKernelComparison

/-! # Consumers of actual eventual kernel annihilation -/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.HomologicalAlgebra
universe u

example {K L : ChainComplex (ModuleCat.{u} ℤ) ℕ} (f : K ⟶ L)
    (hf : ∀ j, Function.Surjective (f.f j)) (p : ℕ → (K ⟶ K))
    (comm : ∀ k, p k ≫ f = f)
    (hp : ∀ k j, HomologicalComplex.homologyMap (p k) j = 𝟙 _)
    (hkill : ∀ j (x : K.X j), f.f j x = 0 → ∃ k, (p k).f j x = 0) :
    QuasiIso f := quasiIso_of_eventual_kernel f hf p comm hp hkill

example (K : ChainComplex (ModuleCat.{u} ℤ) ℕ) : QuasiIso (𝟙 K) := by
  apply quasiIso_of_eventual_kernel (𝟙 K) (fun _ => Function.surjective_id)
    (fun _ => 𝟙 K)
  · intro k
    simp
  · intro k j
    simp
  · intro j x hx
    exact ⟨0, hx⟩
