/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.CechAugmentation

/-! Regression tests for the actual twisted Čech contractions and bicomplex. -/

@[expose] public section

noncomputable section

open CategoryTheory Quillen.LocalCoefficients
open scoped Simplicial

universe u

variable {X : Type u} [TopologicalSpace X] {ι : Type u}
  (U : ι → Set X) (A : System.{u, u} X)

example (n : SimplexCategory) : QuasiIso (cechRowAugmentation U A n) :=
  cechRowAugmentation_quasiIso U A n

example (n : ℕ) : QuasiIso ((cechBicomplexAugmentation U A).f n) :=
  cechBicomplexAugmentation_row_quasiIso U A n

example {m n p q : SimplexCategory} (α : m ⟶ n) (β : p ⟶ q) :
    cechSingularMap U A q α ≫ cechChainMap U A m β =
      cechChainMap U A n β ≫ cechSingularMap U A p α :=
  cechSingularMap_cechChainMap U A α β

example {m n : SimplexCategory} (p : SimplexCategory) (α : m ⟶ n) :
    cechSingularMap U A p α ≫ cechModuleAugmentation U A m p =
      cechModuleAugmentation U A n p ≫ smallChainMap U A α :=
  cechSingularMap_augmentation U A p α

example (n : ℕ) :
    (cechTotalComplex U A).d (n + 2) (n + 1) ≫
      (cechTotalComplex U A).d (n + 1) n = 0 :=
  cechTotalComplex_d_squared U A n

example (n : ℕ) (t : CechSimplex U ⦋n⦌ ⦋0⦌) :
    cechChainInclusion U A t ≫
      (cechBicomplex U A).ιTotal (ComplexShape.down ℕ) n 0 n (Nat.add_zero n) ≫
        (cechSingularAugmentation U A).f n = chainInclusion A t.1.val :=
  cechChainInclusion_singularAugmentation U A n t

example (K : ChainComplex (ModuleCat.{u} ℤ) ℕ) :
    K ≅ (HomologicalComplex₂.single₀Bicomplex K).total (ComplexShape.down ℕ) :=
  HomologicalComplex₂.single₀TotalIso K
