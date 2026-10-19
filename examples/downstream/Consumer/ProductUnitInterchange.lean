/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ProductUnitInterchangeSign

/-! # An additive client of the actual double Laurent unit sign -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent
open Quillen.PerfectComplexes Quillen.PerfectComplexes.ProductUnitInterchange
universe u

/-- The original double unit arrow and its actual Laurent-swap pullback cancel. -/
example (X : Scheme.{u}) :
    doubleLaurentUnitMap X + doubleLaurentUnitMap X ≫
      (boundedFlatPerfectKAddFunctor 2).map
        (baseProductSwapMap (laurentProjection (.of (ULift.{u} ℤ)))
          (laurentProjection (.of (ULift.{u} ℤ))) X).op = 0 := by
  rw [doubleLaurentUnitMap_swap, add_neg_cancel]
