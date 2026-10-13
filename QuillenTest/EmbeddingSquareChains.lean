/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.EmbeddingSquareChains

/-! # Original embedding squares and the degree-zero chain endpoint -/

@[expose] public section

open CategoryTheory HomologicalComplex

universe u

example {S T : ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ)}
    (φ : S ⟶ T) (hS : S.ShortExact) (hT : T.ShortExact)
    (h₁ : QuasiIso φ.τ₁) (h₃ : QuasiIso φ.τ₃) :
    IsIso (homologyMap φ.τ₂ 0) := by
  have := Quillen.homologicalComplex_quasiIso_middle_of_shortExact φ hS hT h₁ h₃
  infer_instance

open Quillen.LocalCoefficients in
example {X₀ X₁ Y₀ Y₁ : Type u}
    [TopologicalSpace X₀] [TopologicalSpace X₁]
    [TopologicalSpace Y₀] [TopologicalSpace Y₁]
    (j : C(X₀, X₁)) (k : C(Y₀, Y₁)) (a : C(X₀, Y₀)) (b : C(X₁, Y₁))
    (w : b.comp j = k.comp a) (A : System.{u, u} Y₁)
    (hj : Topology.IsEmbedding j) (hk : Topology.IsEmbedding k)
    (ha : QuasiIso (pushforwardChainMap a (pullback k A)))
    (hc : QuasiIso (embeddingSquareCokernelMap j k a b w A)) :
    QuasiIso (pushforwardChainMap b A) :=
  pushforwardChainMap_quasiIso_of_embeddingSquare j k a b w A hj hk ha hc
