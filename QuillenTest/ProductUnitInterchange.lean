/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ProductUnitInterchangeSign

/-! # Two actual factor swaps on the original double geometric unit operation -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Products
open Quillen.PerfectComplexes Quillen.PerfectComplexes.ProductUnitInterchange
universe u

/-- Two original geometric swaps recover the original two-unit class in its original order. -/
example {S T : Scheme.{u}} (p : S ⟶ integerBase) (q : T ⟶ integerBase)
    (X : Scheme.{u}) (r : (Γ(S, ⊤))ˣ) (s : (Γ(T, ⊤))ˣ)
    (n : ℕ) (a : BoundedFlatPerfectK X n) :
    boundedFlatPerfectKPullback (baseProductSwapMap q p X) (n + 2)
      (boundedFlatPerfectKPullback (baseProductSwapMap p q X) (n + 2)
        (doubleProjectionUnitOperation q p X s r n a)) =
      doubleProjectionUnitOperation q p X s r n a := by
  rw [doubleProjectionUnitOperation_swap, map_inv, doubleProjectionUnitOperation_swap, inv_inv]
