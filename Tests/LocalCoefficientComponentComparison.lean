/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.LocalCoefficients.ComponentComparison

/-! # Original component restriction with arbitrary component coefficients -/

@[expose] public section

open Quillen.LocalCoefficients

universe u

example {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) (y : Y)
    (hpre : ∀ z, f z ∈ pathComponent y ↔ z ∈ pathComponent x)
    (hf : ∀ B : System.{u, u} Y, QuasiIso (pushforwardChainMap f B))
    (A : System.{u, u} (pathComponent y)) :
    QuasiIso (pushforwardChainMap (componentMap f x y hpre) A) :=
  componentMap_quasiIso f x y hpre hf A
