/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.PerfectComplexes.GilletWaldhausen

/-! # Arbitrary-scheme strict-perfect comparison consumers

These retain the actual Q/S/single forward map, K₀ preimages, both inverse laws,
and the existing triangle to locally-perfect K without asserting its equivalence.
-/
noncomputable section
open Quillen Quillen.PerfectComplexes AlgebraicGeometry
universe u

example (X : Scheme.{u}) (n : ℕ) :
    Function.Bijective (vectorBundleSComparison X n) := vectorBundleSComparison_bijective X n

example (X : Scheme.{u}) (y : StrictK X 0) :
    ∃! x : Quillen.Scheme.K X 0, vectorBundleToStrictKMap X 0 x = y := by
  obtain ⟨x,hx⟩ := (vectorBundleToStrictKMap_bijective X 0).surjective y
  exact ⟨x,hx,fun z hz ↦ (vectorBundleToStrictKMap_bijective X 0).injective (hz.trans hx.symm)⟩

example (X : Scheme.{u}) (n : ℕ) :
    (vectorBundleToStrictKEquiv X n).toMonoidHom = vectorBundleToStrictKMap X n := rfl

example (X : Scheme.{u}) (n : ℕ) (y : StrictK X n) :
    vectorBundleToStrictKMap X n ((vectorBundleToStrictKEquiv X n).symm y) = y :=
  (vectorBundleToStrictKEquiv X n).apply_symm_apply y

example (X : Scheme.{u}) (n : ℕ) (x : Quillen.Scheme.K X n) :
    (vectorBundleToStrictKEquiv X n).symm (vectorBundleToStrictKMap X n x) = x :=
  (vectorBundleToStrictKEquiv X n).symm_apply_apply x

example (X : Scheme.{u}) (n : ℕ) :
    (strictToPerfectKMap X n).comp (vectorBundleToStrictKEquiv X n).toMonoidHom =
      vectorBundleToPerfectKMap X n := rfl
